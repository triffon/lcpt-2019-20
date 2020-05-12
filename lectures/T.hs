data N = O  | S N
  deriving (Eq, Ord, Show, Read)
data B = Tt | Ff
  deriving (Eq, Ord, Show, Read)

split :: (ρ, σ)  ->  (ρ -> σ -> τ) -> τ
split (s, t) f = f s t

cases :: B -> τ -> τ -> τ
cases Tt s t = s
cases Ff s t = t

r :: N -> τ -> (N -> τ -> τ) -> τ
r O     s t = s
r (S n) s t = t n (r n s t)

toInt :: N -> Int
toInt O     = 0
toInt (S n) = 1 + toInt n

toN :: Int -> N
toN 0 = O
toN n = S (toN (n - 1))

p :: N -> N
p n = r n O (\n1 _ -> n1)

z :: N -> B
z n = r n Tt (\n1 p -> Ff)

plus :: N -> N -> N
--plus m n = r m n (\m1 p -> (S p))
plus m n = r m n (const S)
-- plus 0 n == n
-- plus m n == S (plus m1 n)
-- m1 == m - 1
-- p  == plus m1 n == (m - 1) + n

mult :: N -> N -> N
-- mult m n = r m O (\m1 p -> plus n p)
mult m n = r m O (\_ -> plus n)

-- m1 == m - 1
-- p  == mult m1 n == (m - 1) * n

fact :: N -> N
fact n = r n (S O) (\n1 p -> mult (S n1) p)
-- n1 == n - 1
-- p == fact n1 = (n-1)!

eq :: N -> N -> B
eq m = r m z (\_ p n -> r n Ff (\n1 _ -> p n1))
