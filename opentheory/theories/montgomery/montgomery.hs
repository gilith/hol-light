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

threeToTwo :: Bits -> Bits -> Bits -> (Bits,Bits)
threeToTwo =
   \x y z -> let (s,c) = unzip (loop x y z) in (Bits s, Bits c)
  where
    loop :: Bits -> Bits -> Bits -> [(Bool,Bool)]
    loop (Bits []) (Bits []) (Bits []) = []
    loop x y z =
      adder (headBits x) (headBits y) (headBits z) :
      loop (tailBits x) (tailBits y) (tailBits z)

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

twoToTwo :: Bits -> Bits -> (Bits,Bits)
twoToTwo = threeToTwo zeroBits

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

x,y < 3/4 * 2^r
x*y < 9/16 * 2^{2r}

montgomeryReduce n r k x*y < 9/16 * 2^r + n < 2^r

      | r-1 | r-2 | r-3
------+-----+-----+-----
 1*rs |  X  |  X  |  X
 2*rc |  X  |  X  |  X

Let n1 = 2^{r-2} mod n, n2 = 2^{r-1} mod n and n3 = (n1 + n2) mod n.
-}

data StateM =
   StateM
     { xsM :: Bits,
       xcM :: Bits,
       ysM :: Bits,
       ycM :: Bits,
       s1M :: Bits,
       s2M :: Bits,
       sbM :: Bool,
       saM :: Bool,
       szM :: Bool,
       soM :: Bool,
       c1M :: Bits,
       c2M :: Bits,
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
      { xsM = zeroBits,
        xcM = zeroBits,
        ysM = zeroBits,
        ycM = zeroBits,
        s1M = zeroBits,
        s2M = zeroBits,
        sbM = False,
        saM = False,
        szM = False,
        soM = False,
        c1M = zeroBits,
        c2M = zeroBits,
        ksM = zeroBits,
        kcM = zeroBits,
        nsM = zeroBits,
        ncM = zeroBits,
        rsM = zeroBits,
        rcM = zeroBits,
        zsM = zeroBits,
        zcM = zeroBits }

initialM :: Bits -> Bits -> Bits -> Bits -> StateM
initialM xs xc ys yc =
    nullM
      { xsM = xs,
        xcM = xc,
        ysM = ys,
        ycM = yc }

nextM :: Bits -> Int -> Bits -> Bits -> Bits -> Bits -> StateM -> StateM
nextM n r k n1 n2 n3
      (StateM
        { xsM = xs,
          xcM = xc,
          ysM = ys,
          ycM = yc,
          s1M = s1,
          s2M = s2,
          sbM = sb,
          saM = sa,
          szM = sz,
          soM = so,
          c1M = c1,
          c2M = c2,
          ksM = ks,
          kcM = kc,
          nsM = ns,
          ncM = nc,
          rsM = rs,
          rcM = rc,
          zsM = _,
          zcM = _ }) =
    StateM
      { xsM = xs',
        xcM = xc',
        ysM = ys',
        ycM = yc',
        s1M = s1',
        s2M = s2',
        sbM = sb',
        saM = sa',
        szM = sz',
        soM = so',
        c1M = c1',
        c2M = c2',
        ksM = ks',
        kcM = kc',
        nsM = ns',
        ncM = nc',
        rsM = rs',
        rcM = rc',
        zsM = zs',
        zcM = zc' }
  where
    (xs',xc') = twoToTwo (tailBits xs) xc
    ys' = ys
    yc' = yc
    (s1',c1') = threeToTwo (if headBits xs then ys else zeroBits)
                  (if headBits xs then (consBits False yc) else zeroBits) c1
    (s2',c2') = threeToTwo (tailBits s1) (tailBits s2) c2
    (sa',sb') = adder (headBits s1) (headBits s2) sb
    sz' = sa
    so' = so || sz
    (ks',kc') = threeToTwo (if sa then k else zeroBits) (tailBits ks) kc
    (ns',nc') = threeToTwo (if (headBits ks) then n else zeroBits)
                  (tailBits ns) nc
    (rs',rc') = fourToTwo
                  (tailBits ns)
                  nc
                  (consBits sz (consBits sa s2))
                  (consBits so (consBits False (consBits sb c2)))
    (zs',zc') =
        threeToTwo
          (if nthBits (r - 1) rs || nthBits (r - 2) rc
             then if nthBits (r - 2) rs || nthBits (r - 3) rc
                    then n3
                    else n2
             else if nthBits (r - 2) rs
                    then if nthBits (r - 3) rc then n2 else n1
                    else if nthBits (r - 3) rc then n1 else zeroBits)
          (prefixBits (r - 2) rs)
          (consBits False (prefixBits (r - 3) rc))

montgomerySquare :: Natural -> Int -> Natural -> Bits -> Bits -> [StateM]
montgomerySquare n r k xs xc =
    mkCircuit next initial
  where
    initial = initialM xs xc xs xc

    next = nextM (numToBits n) r (numToBits k)
             (numToBits n1) (numToBits n2) (numToBits n3)

    n1 = pow2 (r - 2) `mod` n
    n2 = (2 * n1) `mod` n
    n3 = (3 * n1) `mod` n

montgomerySquareProp ::
    Natural -> Int -> Natural -> Natural -> Bits -> Bits -> Bool
montgomerySquareProp n r s k xs xc =
    and [xasCorrect,
         sasCorrect,
         kssCorrect,
         nssCorrect,
         nssLCorrect,
         nssHCorrect,
         sasHCorrect,
         soCorrect,
         redCorrect,
         redBound,
         resCorrect,
         resBound]
  where
    ckt = montgomerySquare n r k xs xc

    xas = bitsToNum (Bits (take r (map (headBits . xsM) ckt)))
    xasCorrect = xas == bitsToNum xs + 2 * bitsToNum xc

    sas = bitsToNum (Bits (take (2 * r) (map saM (drop 2 ckt))))
    sasCorrect = sas == xas * xas

    kss = bitsToNum (Bits (take r (map (headBits . ksM) (drop 3 ckt))))
    kssCorrect = kss == (sas * k) `mod` pow2 r

    nssCorrect = (kss * n + sas) `mod` pow2 r == 0

    nssL = bitsToNum (Bits (take r (map (headBits . nsM) (drop 4 ckt))))
    nssLCorrect = nssL == (kss * n) `mod` pow2 r

    cktR = head (drop (r + 3) ckt)

    nssH = bitsToNum (tailBits (nsM cktR)) + bitsToNum (ncM cktR)
    nssHCorrect = nssH == (kss * n) `div` pow2 r

    sasH = boolToNum (szM cktR) + 2 * (boolToNum (saM cktR) + 2 * (bitsToNum (s2M cktR) + boolToNum (sbM cktR) + 2 * bitsToNum (c2M cktR)))
    sasHCorrect = sasH == sas `div` pow2 r

    so = boolToNum (soM cktR)
    soCorrect = (sasH + nssH + so) `mod` n == (sas * s) `mod` n

    cktR' = head (drop (r + 4) ckt)

    red = bitsToNum (rsM cktR') + 2 * bitsToNum (rcM cktR')
    redCorrect = red `mod` n == (sas * s) `mod` n
    redBound = red < pow2 r

    cktR'' = head (drop (r + 5) ckt)

    res = bitsToNum (zsM cktR'') + 2 * bitsToNum (zcM cktR'')
    resCorrect = res `mod` n == (sas * s) `mod` n
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
