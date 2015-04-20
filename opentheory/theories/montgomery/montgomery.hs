-- ============================================================================
-- HASKELL PROTOTYPE OF A HARDWARE MONTGOMERY MULTIPLIER
-- Joe Leslie-Hurd
-- ============================================================================

{-
To use the prototype first install the following required cabal package:

  cabal install opentheory

Then load the prototype:

  ghci montgomery.hs

Finally run some QuickCheck tests on it:

  main
-}


module Main
where

import qualified OpenTheory.Data.List as List
import OpenTheory.Primitive.Natural
import OpenTheory.Primitive.Random
import OpenTheory.Primitive.Test
import OpenTheory.Number.Natural
import qualified OpenTheory.Number.Natural.Bits as Bits
import qualified OpenTheory.Number.Natural.Geometric as Geometric

-------------------------------------------------------------------------------
-- Utility functions
-------------------------------------------------------------------------------

pow2 :: Int -> Natural
pow2 n = if n <= 0 then 1 else 2 * pow2 (n - 1)

egcd :: Natural -> Natural -> (Natural,Natural,Natural)
egcd a b =
    if b == 0
      then (1,0,a)
      else
        if a <= b
          then
            let q = b `div` a in
            let b' = b - q * a in
            let (s,t,g) = egcd a b' in
            (s + q * t, t, g)
          else
            let q = a `div` b in
            let a' = a - q * b in
            if a' == 0
              then (1, q - 1, b)
              else
                let (s,t,g) = egcd a' b in
                (s, q * s + t, g)

egcdProp :: Natural -> Natural -> Bool
egcdProp a b =
    and [divides1,
         divides2,
         smallest]
  where
    divides1 = divides g a

    divides2 = divides g b

    smallest = s * a == t * b + g

    (s,t,g) = egcd a b

egcdCorrect :: IO ()
egcdCorrect =
    check "|- ~(a = 0) /\\ egcd a b = (s,t,g) ==>\n   divides g a /\\ divides g b /\\ s * a = t * b + g\n" prop
  where
    prop r0 =
      egcdProp (a + 1) b
        where
      (a,r1) = random r0
      (b,_) = random r1

-------------------------------------------------------------------------------
-- Individual bits
-------------------------------------------------------------------------------

bitToNum :: Bool -> Natural
bitToNum x = if x then 1 else 0

numToBit :: Natural -> Bool
numToBit n =
    if n < 2
      then n == 1
      else error $ "numToBit: out of range: " ++ show n

-- A full adder

adder :: Bool -> Bool -> Bool -> (Bool,Bool)
adder x y z =
  let s = (x == y) == z in
  let c = (x && y) || (x && z) || (y && z) in
  (s,c)

adderProp :: Bool -> Bool -> Bool -> Bool
adderProp x y z =
    bitToNum x + bitToNum y + bitToNum z == bitToNum s + 2 * bitToNum c
  where
    (s,c) = adder x y z

adderCorrect :: IO ()
adderCorrect = check "|- adder x y z = (s,c) ==>\n   b2n x + b2n y + b2n z = b2n s + 2 * b2n c\n" adderProp

-------------------------------------------------------------------------------
-- Streams of bits
-------------------------------------------------------------------------------

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

dropBits :: Int -> Bits -> Bits
dropBits n b =
    if n == 0
      then b
      else dropBits (n - 1) (tailBits b)

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
bitsToNum x = bitToNum (headBits x) + 2 * bitsToNum (tailBits x)

randomBits :: Random -> (Bits,Random)
randomBits r =
    (numToBits n, r')
  where
    (n,r') = random r

randomPrefixBits :: Int -> Random -> (Bits,Random)
randomPrefixBits k r =
    (prefixBits k n, r')
  where
    (n,r') = randomBits r

instance Show Bits where
  show x = show (bitsToNum x) ++ ":[" ++ show (widthBits x) ++ "]"

randomLength :: Random -> (Natural,Random)
randomLength = Geometric.random

-- A 3:2 compressor

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

-------------------------------------------------------------------------------
-- Circuits
-------------------------------------------------------------------------------

mkCircuit :: (s -> s) -> s -> [s]
mkCircuit next =
    mk
  where
    mk s = s : mk (next s)

-------------------------------------------------------------------------------
-- Low fan-in counters
-------------------------------------------------------------------------------

data StateC =
   StateC
     { srC :: Bits,
       crC :: Bits,
       dnC :: Bool }
  deriving Show

nullC :: StateC
nullC =
    StateC
      { srC = zeroBits,
        crC = zeroBits,
        dnC = False }

initialC :: Bits -> StateC
initialC nb =
    nullC
      { srC = tailBits nb,
        crC = prefixBits 1 nb }

nextC :: Int -> StateC -> StateC
nextC r
      (StateC
        { srC = sr,
          crC = cr,
          dnC = dn }) =
    StateC
      { srC = sr',
        crC = cr',
        dnC = dn' }
  where
    (sr',cr1') = -- [r-1,r-1]
        twoToTwo sr (prefixBits (r - 1) cr)

    cr0' = -- [1]
        not (headBits cr)

    cr' = -- [r]
        consBits cr0' cr1'

    dn' = -- [1]
        dn || nthBits (r - 1) cr

counter :: Natural -> [StateC]
counter n =
    mkCircuit next initial
  where
    initial = initialC nb

    next = nextC r

    r = widthBits (numToBits n)

    nb = numToBits (pow2 r + fromIntegral r - (n + 1))

counterProp :: Natural -> Natural -> Bool
counterProp n t =
    and [dnCorrect,
         sumCorrect,
         carryCorrect]
  where
    r = widthBits (numToBits n)
    nb = numToBits (pow2 r + fromIntegral r - (n + 1))

    ckt = counter n !! (fromIntegral t)

    sr = srC ckt
    cr = crC ckt
    dn = dnC ckt

    dnCorrect = dn == (n <= t)

    -- At time t = n - r, we expect sr + cr to be 2^{r-1}
    sumCorrect =
      not (t < n) ||
      (2 * (bitsToNum sr + bitsToNum cr) + (if headBits cr then 0 else 1) + n
       ==
       pow2 r + fromIntegral r + t)

    carryCorrect =
      not (n - fromIntegral r <= t && t < n) ||
      (let k = r - fromIntegral (n - t) in
       (bitsToNum (dropBits k sr) + bitsToNum (dropBits k cr)
        ==
        pow2 (r - (k + 1)))
       &&
       nthBits k cr)

counterCorrect :: IO ()
counterCorrect =
    check "Testing properties of the low fan-in counter\n" prop
  where
    prop r0 =
      counterProp (n + 1) t
        where
      (n,r1) = random r0
      (t,_) = random r1

-------------------------------------------------------------------------------
-- Montgomery multiplication
-------------------------------------------------------------------------------

{-
Suppose we are given a large odd integer n, and we would like to carry
out an arithmetic computation modulo n. Addition modulo n is easy to
calculate with the help of the simplemod function:

simplemod n x = if x < n then x else simplemod n (x - n)

Then

(x + y) mod n = ((x mod n) + (y mod n)) mod n
              = simplemod n ((x mod n) + (y mod n))

Problem: It is expensive to compute multiplication modulo n, mainly
because calculating (x * y) mod n requires a costly integer remainder
operation.

Well, here's an interesting fact discovered by Montgomery. Pick an
integer r such that n < 2^r. Since gcd(2^r,n) = 1, we can find k and s
satisfying 2^r * s = k * n + 1. Then the function

montgomery_reduce n r k xy =
  (xy + ((xy * k) mod 2^r) * n) div 2^r

doesn't require any integer remainder operations (just shifts and
masks) and satisfies the following two properties:

1. montgomery_reduce n r k xy mod n = (xy * s) mod n

2. xy <= 2^r * m ==> montgomery_reduce n r k xy < m + n

How does this help? Define the Montgomery monad M(x) = (x * 2^r) mod
n. Then Montgomery addition is just like regular modular addition:

M(x + y) = ((x + y) * 2^r) mod n
         = ((x * 2^r) mod n + (y * 2^r) mod n) mod n
         = (M(x) + M(y)) mod n
         = simplemod n (M(x) + M(y))

and Montgomery multiplication works as follows:

M(x * y) = ((x * y) * 2^r) mod n
         = (((x * 2^r) mod n) * ((y * 2^r) mod n) * s) mod n
         = ((M(x) * M(y)) * s) mod n
         = montgomery_reduce n r k (M(x) * M(y)) mod n
         = simplemod n (montgomery_reduce n r k (M(x) * M(y)))

We can carry out a modular arithmetic computation f in the Montgomery
monad M using the following procedure:

1. Lift every input x to M(x) by computing M(x) = (x * 2^r) mod n.

2. Use the above arithmetic procedures to compute M(f(x)) from M(x).

3. Drop the result M(f(x)) to the output f(x) by computing

  simplemod n (montgomery_reduce n r k (M(f(x)))

Note that using the Montgomery monad to perform a modular arithmetic
computation is only worth it if the number of multiplications it
involves is greater than the number of inputs, because Step 1 uses a
modular multiplication to lift every input into the monad.

It is possible to Montgomery multiplication in hardware. In our
implementation we use a slightly larger r parameter so that
n < 2^{r-2}, and represent Montgomery values in sum-carry format:

x = xs:[r-2] + 2 * xc:[r-2]
y = ys:[r-2] + 2 * yc:[r-2]

By the representation

x,y <= 2^{r-2} - 1 + 2 * (2^{r-2} - 1)
     < 1/4 * 2^r + 1/2 * 2^r
     = 3/4 * 2^r

Therefore

x * y < 9/16 * 2^{2r}

The circuit will compute montgomery_reduce n r k (x * y) in sum-carry
format as

rs:[r] + 2 * rc:[r-1]

where by Montgomery Property 2

rs+2*rc < 9/16 * 2^r + n < 2^r

Consider the bits of rs and 2*rc:

      | r-1 | r-2 | r-3
------+-----+-----+-----
   rs |  A  |  B  |  X
 2*rc |  C  |  D  |  X

Precompute

  rx = 2^{r-2} mod n
  ry = (2 * rx) mod n
  rz = (3 * rx) mod n

rs+2*rc is the correct result modulo n. To construct a result that
fits into r-2 bits in sum-carry format (like the inputs), we will
subtract

A * 2^{r-1} + B * 2^{r-2}

from rs, and

C * 2^{r-1} + D * 2^{r-2}

from 2*rc. To preserve the result modulo n, we therefore need to add

case (2 * (A + B)) + (C + D) of
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

    (ks',kc') = -- [r-1,r-1]
        threeToTwo (if sy then k else zeroBits) (tailBits ks) kc

    (ns',nc') = -- [r-2,r-2]
        threeToTwo (if (headBits ks) then n else zeroBits)
          (tailBits ns) nc

    (rs',rc') = -- [r,r-1]  (by the bounds theorem)
        fourToTwo
          (tailBits ns)                                     -- [r-3]
          nc                                                -- [r-2]
          (consBits sz (consBits sy sb))                    -- [r]
          (consBits so (consBits False (consBits sx cb)))   -- [r+1]

    (zs',zc') = -- [r-2,r-2]
        threeToTwo
          (let c = nthBits (r - 1) rs || nthBits (r - 2) rc ||
                   (nthBits (r - 2) rs && nthBits (r - 3) rc) in
           let s = nthBits (r - 2) rs /= nthBits (r - 3) rc in
           case (c,s) of
             (False,False) -> zeroBits
             (False,True) -> rx
             (True,False) -> ry
             (True,True) -> rz)
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

    sysH = bitToNum (szM cktR) + 2 * (bitToNum (syM cktR) + 2 * (bitsToNum (sbM cktR) + bitToNum (sxM cktR) + 2 * bitsToNum (cbM cktR)))
    sysHCorrect = sysH == sys `div` pow2 r

    so = bitToNum (soM cktR)
    soCorrect = (sysH + nssH + so) `mod` n == (sys * s) `mod` n

    cktR' = head (drop (r + 4) ckt)

    red = bitsToNum (rsM cktR') + 2 * bitsToNum (rcM cktR')
    redCorrect = red `mod` n == (sys * s) `mod` n
    redBound = red < pow2 r

    cktR'' = head (drop (r + 5) ckt)

    res = bitsToNum (zsM cktR'') + 2 * bitsToNum (zcM cktR'')
    resCorrect = res `mod` n == (sys * s) `mod` n
    resBound = res <= pow2 r - 2

montgomeryParameters :: Natural -> (Int,Natural,Natural)
montgomeryParameters n =
    (r,s,k)
  where
    r = widthBits (numToBits n) + 2
    (s,k,_) = egcd (pow2 r) n

montgomerySquareCorrect :: IO ()
montgomerySquareCorrect =
    check "Testing properties of montgomerySquare\n" prop
  where
    prop r0 =
      montgomerySquareProp n r s k xs xc
        where
      (m,r1) = random r0
      n = 2 * m + 1
      (r,s,k) = montgomeryParameters n
      (xs,r2) = randomPrefixBits (r - 2) r1
      (xc,_) = randomPrefixBits (r - 2) r2

-------------------------------------------------------------------------------
-- Testing
-------------------------------------------------------------------------------

main :: IO ()
main =
    do egcdCorrect
       adderCorrect
       threeToTwoCorrect
       counterCorrect
       montgomerySquareCorrect

-------------------------------------------------------------------------------
-- Development
-------------------------------------------------------------------------------

{-
n :: Natural
--n = 35
n = 23

r :: Int
--r = 8
r = 7

s :: Natural
--s = 16
s = 7

k :: Natural
--k = 117
k = 39

xs :: Bits
--xs = numToBits (pow2 (r - 2) - 1)
xs = numToBits 8

xc :: Bits
--xc = numToBits (pow2 (r - 2) - 1)
xc = numToBits 2

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

sysH = bitToNum (szM cktR) + 2 * (bitToNum (syM cktR) + 2 * (bitsToNum (sbM cktR) + bitToNum (sxM cktR) + 2 * bitsToNum (cbM cktR)))
sysHCorrect = sysH == sys `div` pow2 r

so = bitToNum (soM cktR)
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
