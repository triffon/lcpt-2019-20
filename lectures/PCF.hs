data N = O  | S N
  deriving (Eq, Ord, Show, Read)
data B = Tt | Ff
  deriving (Eq, Ord, Show, Read)

split :: (ρ, σ)  ->  (ρ -> σ -> τ) -> τ
split (s, t) f = f s t

p :: N -> N
p O     = O
p (S n) = n

z :: N -> B
z O     = Tt
z (S n) = Ff

cases :: B -> τ -> τ -> τ
cases Tt s t = s
cases Ff s t = t

y :: (τ -> τ) -> τ
y t = t (y t)

toInt :: N -> Int
toInt O     = 0
toInt (S n) = 1 + toInt n

toN :: Int -> N
toN 0 = O
toN n = S (toN (n - 1))

γplus1 :: (N -> N -> N) -> N -> N -> N
γplus1 f m n = cases (z n) m (S (f m (p n)))
plus1 = y γplus1

γplus2 :: N -> (N -> N) -> N -> N
γplus2 m f n = cases (z n) m (S (f (p n)))
-- plus2 m = y (γplus2 m)
plus2 = y . γplus2

plus = plus1

γmult :: N -> (N -> N) -> N -> N
γmult m f n = cases (z n) O (plus m (f (p n)))
mult = y . γmult

γfact :: (N -> N) -> N -> N
γfact f n = cases (z n) (S O) (mult n (f (p n)))
fact = y γfact
