module Main
where

import qualified OpenTheory.Data.List as List
import OpenTheory.Primitive.Natural
import OpenTheory.Primitive.Random
import OpenTheory.Primitive.Test
import OpenTheory.Number.Natural
import qualified OpenTheory.Number.Natural.Bits as Bits
import qualified OpenTheory.Number.Natural.Geometric as Geometric

{- Utility functions -}

pow2 :: Int -> Natural
pow2 n = if n <= 0 then 1 else 2 * pow2 (n - 1)

{- Individual bits -}

boolToNum :: Bool -> Natural
boolToNum x = if x then 1 else 0

numToBool :: Natural -> Bool
numToBool n =
    if n < 2
      then n == 1
      else error $ "numToBool: out of range: " ++ show n

{- A full adder -}

adder :: Bool -> Bool -> Bool -> (Bool,Bool)
adder x y z =
  let s = (x == y) == z in
  let c = (x && y) || (x && z) || (y && z) in
  (s,c)

adderProp :: Bool -> Bool -> Bool -> Bool
adderProp x y z =
    boolToNum x + boolToNum y + boolToNum z == boolToNum s + 2 * boolToNum c
  where
    (s,c) = adder x y z

adderCorrect :: IO ()
adderCorrect = check "|- adder x y z = (s,c) ==>\n   b2n x + b2n y + b2n z = b2n s + 2 * b2n c\n" adderProp

{- Streams of bits -}

data Bits = Bits [Bool]

zeroBits :: Bits
zeroBits = Bits []

widthBits :: Bits -> Int
widthBits (Bits l) = length l

consBits :: Bool -> Bits -> Bits
consBits h (Bits t) = Bits (h : t)

headBits :: Bits -> Bool
headBits (Bits []) = False
headBits (Bits (h : _)) = h

tailBits :: Bits -> Bits
tailBits (Bits []) = zeroBits
tailBits (Bits (_ : t)) = Bits t

prefixBits :: Int -> Bits -> Bits
prefixBits _ (Bits []) = zeroBits
prefixBits n (Bits (h : t)) =
    if n == 0
      then zeroBits
      else consBits h (prefixBits (n - 1) (Bits t))

nthBits :: Int -> Bits -> Bool
nthBits n b = if n == 0 then headBits b else nthBits (n - 1) (tailBits b)

numToBits :: Natural -> Bits
numToBits n =
    if n == 0
      then zeroBits
      else consBits (n `mod` 2 == 1) (numToBits (n `div` 2))

bitsToNum :: Bits -> Natural
bitsToNum (Bits []) = 0
bitsToNum x = boolToNum (headBits x) + 2 * bitsToNum (tailBits x)

randomBits :: Random -> (Bits,Random)
randomBits r =
    (numToBits n, r')
  where
    (n,r') = fromRandom r

randomPrefixBits :: Int -> Random -> (Bits,Random)
randomPrefixBits k r =
    (prefixBits k n, r')
  where
    (n,r') = randomBits r

instance Show Bits where
  show x = show (bitsToNum x) ++ ":[" ++ show (widthBits x) ++ "]"

randomLength :: Random -> (Natural,Random)
randomLength = Geometric.fromRandom

{- A 3:2 compressor -}

twoToTwo :: Bits -> Bits -> (Bits,Bits)
twoToTwo (Bits []) ys = (ys,zeroBits)
twoToTwo xs (Bits []) = (xs,zeroBits)
twoToTwo (Bits (x : xs)) (Bits (y : ys)) =
    (consBits s ss, consBits c cs)
  where
    (s,c) = adder x y False
    (ss,cs) = twoToTwo (Bits xs) (Bits ys)

threeToTwo :: Bits -> Bits -> Bits -> (Bits,Bits)
threeToTwo (Bits []) ys zs = twoToTwo ys zs
threeToTwo xs (Bits []) zs = twoToTwo xs zs
threeToTwo xs ys (Bits []) = twoToTwo xs ys
threeToTwo (Bits (x : xs)) (Bits (y : ys)) (Bits (z : zs)) =
    (consBits s ss, consBits c cs)
  where
    (s,c) = adder x y z
    (ss,cs) = threeToTwo (Bits xs) (Bits ys) (Bits zs)

threeToTwoProp :: Bits -> Bits -> Bits -> Bool
threeToTwoProp x y z =
    bitsToNum x + bitsToNum y + bitsToNum z ==
    bitsToNum s + 2 * bitsToNum c
  where
    (s,c) = threeToTwo x y z

threeToTwoCorrect :: IO ()
threeToTwoCorrect =
    check "|- 3to2 x y z = (s,c) ==>\n   s2n r x + s2n r y + s2n r z = s2n r s + 2 * s2n r c\n" prop
  where
    prop r0 =
      threeToTwoProp x y z
        where
      (x,r1) = randomBits r0
      (y,r2) = randomBits r1
      (z,_) = randomBits r2

fourToTwo :: Bits -> Bits -> Bits -> Bits -> (Bits,Bits)
fourToTwo w x y z =
    threeToTwo w s (consBits False c)
  where
    (s,c) = threeToTwo x y z

{- Circuits -}

mkCircuit :: (s -> s) -> s -> [s]
mkCircuit next =
    mk
  where
    mk s = s : mk (next s)

{- Montgomery multiplication -}

{-
Let n < 2^{r-2}, and represent inputs as

x = xs:[r-2] + 2 * xc:[r-2]
y = ys:[r-2] + 2 * yc:[r-2]

x,y <= 2^{r-2} - 1 + 2 * (2^{r-2} - 1)
     < 1/4 * 2^r + 1/2 * 2^r
     = 3/4 * 2^r

x*y < 9/16 * 2^{2r}

Represent montgomeryReduce n (2^r) k (x*y) as

rs:[r] + 2 * rc:[r-1]

rs+2*rc < 9/16 * 2^r + n < 2^r

      | r-1 | r-2 | r-3
------+-----+-----+-----
   rs |  A  |  B  |  X
 2*rc |  C  |  D  |  X

Let rx = 2^{r-2} mod n, ry = (2 * rx) mod n and rz = (3 * rx) mod n.

rs+2*rc is the correct result modulo n. To construct a result that
fits into r-2 bits, we will subtract

A * 2^{r-1} + B * 2^{r-2}

from rs, and

C * 2^{r-1} + D * 2^{r-2}

from 2*rc. To preserve the result modulo n, we therefore need to add

case 2 * (A + B) + (C + D) of
  0 => 0
| 1 => rx
| 2 => ry
| 3 => rz
-}

data StateM =
   StateM
     { ysM :: Bits,
       ycM :: Bits,
       saM :: Bits,
       sbM :: Bits,
       sxM :: Bool,
       syM :: Bool,
       szM :: Bool,
       soM :: Bool,
       caM :: Bits,
       cbM :: Bits,
       ksM :: Bits,
       kcM :: Bits,
       nsM :: Bits,
       ncM :: Bits,
       rsM :: Bits,
       rcM :: Bits,
       zsM :: Bits,
       zcM :: Bits }
  deriving Show

nullM :: StateM
nullM =
    StateM
      { ysM = zeroBits,
        ycM = zeroBits,
        saM = zeroBits,
        sbM = zeroBits,
        sxM = False,
        syM = False,
        szM = False,
        soM = False,
        caM = zeroBits,
        cbM = zeroBits,
        ksM = zeroBits,
        kcM = zeroBits,
        nsM = zeroBits,
        ncM = zeroBits,
        rsM = zeroBits,
        rcM = zeroBits,
        zsM = zeroBits,
        zcM = zeroBits }

initialM :: Bits -> Bits -> StateM
initialM ys yc =
    nullM
      { ysM = ys,
        ycM = yc }

nextM :: Bits -> Int -> Bits -> Bits -> Bits -> Bits -> Bits -> Bits ->
         StateM -> StateM
nextM n r k rx ry rz xs xc
      (StateM
        { ysM = ys,
          ycM = yc,
          saM = sa,
          sbM = sb,
          sxM = sx,
          syM = sy,
          szM = sz,
          soM = so,
          caM = ca,
          cbM = cb,
          ksM = ks,
          kcM = kc,
          nsM = ns,
          ncM = nc,
          rsM = rs,
          rcM = rc,
          zsM = _,
          zcM = _ }) =
    StateM
      { ysM = ys',
        ycM = yc',
        saM = sa',
        sbM = sb',
        sxM = sx',
        syM = sy',
        szM = sz',
        soM = so',
        caM = ca',
        cbM = cb',
        ksM = ks',
        kcM = kc',
        nsM = ns',
        ncM = nc',
        rsM = rs',
        rcM = rc',
        zsM = zs',
        zcM = zc' }
  where
    (ys',yc') = -- [r-2,r-2]
        twoToTwo (tailBits ys) yc

    (sa',ca') = -- [r-1,r-2]
        threeToTwo (if headBits ys then xs else zeroBits)
          (if headBits ys then (consBits False xc) else zeroBits) ca

    (sb',cb') = -- [r-2,r-2]
        threeToTwo (tailBits sa) (tailBits sb) cb

    (sy',sx') = -- [1,1]
        adder (headBits sa) (headBits sb) sx

    sz' = sy -- [1]

    so' = so || sz -- [1]

    (ks',kc') = -- [r]
        threeToTwo (if sy then k else zeroBits) (tailBits ks) kc

    (ns',nc') = -- [r-2,r-2]
        threeToTwo (if (headBits ks) then n else zeroBits)
          (tailBits ns) nc

    (rs',rc') = -- [r,r]  (by the bounds theorem)
        fourToTwo
          (tailBits ns)
          nc
          (consBits sz (consBits sy sb))
          (consBits so (consBits False (consBits sx cb)))

    (zs',zc') = -- [r-2,r-2]
        threeToTwo
          (if nthBits (r - 1) rs || nthBits (r - 2) rc
             then if nthBits (r - 2) rs || nthBits (r - 3) rc
                    then rz
                    else ry
             else if nthBits (r - 2) rs
                    then if nthBits (r - 3) rc then ry else rx
                    else if nthBits (r - 3) rc then rx else zeroBits)
          (prefixBits (r - 2) rs)
          (consBits False (prefixBits (r - 3) rc))

montgomerySquare :: Natural -> Int -> Natural -> Bits -> Bits -> [StateM]
montgomerySquare n r k xs xc =
    mkCircuit next initial
  where
    initial = initialM xs xc

    next = nextM (numToBits n) r (numToBits k)
             (numToBits rx) (numToBits ry) (numToBits rz)
             xs xc

    rx = pow2 (r - 2) `mod` n
    ry = (2 * rx) `mod` n
    rz = (3 * rx) `mod` n

montgomerySquareProp ::
    Natural -> Int -> Natural -> Natural -> Bits -> Bits -> Bool
montgomerySquareProp n r s k xs xc =
    and [xasCorrect,
         sysCorrect,
         kssCorrect,
         nssCorrect,
         nssLCorrect,
         nssHCorrect,
         sysHCorrect,
         soCorrect,
         redCorrect,
         redBound,
         resCorrect,
         resBound]
  where
    ckt = montgomerySquare n r k xs xc

    xas = bitsToNum (Bits (take r (map (headBits . ysM) ckt)))
    xasCorrect = xas == bitsToNum xs + 2 * bitsToNum xc

    sys = bitsToNum (Bits (take (2 * r) (map syM (drop 2 ckt))))
    sysCorrect = sys == xas * xas

    kss = bitsToNum (Bits (take r (map (headBits . ksM) (drop 3 ckt))))
    kssCorrect = kss == (sys * k) `mod` pow2 r

    nssCorrect = (kss * n + sys) `mod` pow2 r == 0

    nssL = bitsToNum (Bits (take r (map (headBits . nsM) (drop 4 ckt))))
    nssLCorrect = nssL == (kss * n) `mod` pow2 r

    cktR = head (drop (r + 3) ckt)

    nssH = bitsToNum (tailBits (nsM cktR)) + bitsToNum (ncM cktR)
    nssHCorrect = nssH == (kss * n) `div` pow2 r

    sysH = boolToNum (szM cktR) + 2 * (boolToNum (syM cktR) + 2 * (bitsToNum (sbM cktR) + boolToNum (sxM cktR) + 2 * bitsToNum (cbM cktR)))
    sysHCorrect = sysH == sys `div` pow2 r

    so = boolToNum (soM cktR)
    soCorrect = (sysH + nssH + so) `mod` n == (sys * s) `mod` n

    cktR' = head (drop (r + 4) ckt)

    red = bitsToNum (rsM cktR') + 2 * bitsToNum (rcM cktR')
    redCorrect = red `mod` n == (sys * s) `mod` n
    redBound = red < pow2 r

    cktR'' = head (drop (r + 5) ckt)

    res = bitsToNum (zsM cktR'') + 2 * bitsToNum (zcM cktR'')
    resCorrect = res `mod` n == (sys * s) `mod` n
    resBound = res <= pow2 r - 2

montgomerySquareCorrect :: Natural -> Int -> Natural -> Natural -> IO ()
montgomerySquareCorrect n r s k =
    check "montgomerySquare is correct\n" prop
  where
    prop r0 =
      montgomerySquareProp n r s k xs xc
        where
      (xs,r1) = randomPrefixBits (r - 2) r0
      (xc,_) = randomPrefixBits (r - 2) r1

main :: IO ()
main =
    do adderCorrect
       threeToTwoCorrect
       montgomerySquareCorrect 35 8 16 117

{- Testing
n :: Natural
n = 35

r :: Int
r = 8

s :: Natural
s = 16

k :: Natural
k = 117

xs = numToBits (pow2 (r - 2) - 1)
xc = numToBits (pow2 (r - 2) - 1)

ckt = montgomerySquare n r k xs xc

xas = bitsToNum (Bits (take r (map (headBits . ysM) ckt)))
xasCorrect = xas == bitsToNum xs + 2 * bitsToNum xc

sys = bitsToNum (Bits (take (2 * r) (map syM (drop 2 ckt))))
sysCorrect = sys == xas * xas

kss = bitsToNum (Bits (take r (map (headBits . ksM) (drop 3 ckt))))
kssCorrect = kss == (sys * k) `mod` pow2 r

nssCorrect = (kss * n + sys) `mod` pow2 r == 0

nssL = bitsToNum (Bits (take r (map (headBits . nsM) (drop 4 ckt))))
nssLCorrect = nssL == (kss * n) `mod` pow2 r

cktR = head (drop (r + 3) ckt)

nssH = bitsToNum (tailBits (nsM cktR)) + bitsToNum (ncM cktR)
nssHCorrect = nssH == (kss * n) `div` pow2 r

sysH = boolToNum (szM cktR) + 2 * (boolToNum (syM cktR) + 2 * (bitsToNum (sbM cktR) + boolToNum (sxM cktR) + 2 * bitsToNum (cbM cktR)))
sysHCorrect = sysH == sys `div` pow2 r

so = boolToNum (soM cktR)
soCorrect = (sysH + nssH + so) `mod` n == (sys * s) `mod` n

cktR' = head (drop (r + 4) ckt)

red = bitsToNum (rsM cktR') + 2 * bitsToNum (rcM cktR')
redCorrect = red `mod` n == (sys * s) `mod` n
redBound = red < pow2 r

cktR'' = head (drop (r + 5) ckt)

res = bitsToNum (zsM cktR'') + 2 * bitsToNum (zcM cktR'')
resCorrect = res `mod` n == (sys * s) `mod` n
resBound = res <= pow2 r - 2
-}
