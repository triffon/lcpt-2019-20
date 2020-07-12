# Agda задачи
За задачите се предполага че имате поне следните дефиниции, които сме ползвали по време на упражнение:
```agda
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data _==_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x == x

ap : {A B : Set} {x y : A} (f : A -> B) -> x == y -> f x == f y
ap f refl = refl

infix 15 _==_
{-# BUILTIN EQUALITY _==_ #-}

_<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f << g) x = f (g x)

id : {A : Set} -> A -> A
id x = x

data Vector (A : Set) : Nat -> Set where
  [] : Vector A zero
  _,-_ : {n : Nat} -> A -> Vector A n -> Vector A (suc n)
```

## 0. (3т.) `Applicative` и законите му, за вектори

Имплементирайте следните функции:
```agda
vpure : {A : Set} (n : Nat) -> A -> Vector A n

_<v>_ : {A B : Set} {n : Nat} -> Vector (A -> B) n -> Vector A n -> Vector B n

infixl 25 _<v>_
```

`vpure` е "клониране" на стойност `n`, получавайки вектор от стойността много пъти, с дължина `n`.

`_<v>_` е "поточково" прилагане на един вектор от функции към друг от стойности - `zipWith` от `Haskell`, като
сме си подсигурили че дължините им са еднакви предварително, за разлика от `zipWith` в `Haskell`.

Освен че са полезни сами по себе си, тези функции също така и са нещото което прави `Vector` инстанция на `Applicative` от `Haskell`.
(В `Haskell` тази инстанция е реализирана чрез `newtype`-а `ZipList`.)

За разлика от `Haskell` обаче, тук имаме възможността да формулираме и докажем **законите**, които трябва да изпълнява един `Applicative`.

Те са (взето от [Typeclassopedia-та](https://wiki.haskell.org/Typeclassopedia), където има и някакви обяснения за тях):
```haskell
pure id <*> v == v                            -- Identity
pure f <*> pure x == pure (f x)               -- Homomorphism
u <*> pure y == pure (\f -> f y) <*> u        -- Interchange
pure (.) <*> u <*> v <*> w == u <*> (v <*> w) -- Composition
```

Задачата ви е да измислите подходящ превод за тях на Agda за конкретно `vpure` (вместо `pure`) и `_<v>_` (вместо `(<*>)`), както и да ги докажете в последствие.

## 1. (3т.) Транспониране на матрици

Имплементирайте `map` за вектори:

```agda
vmap : {A B : Set} {n : Nat} -> (A -> B) -> Vector A n -> Vector B n
```

`Matrix` (матрица) с размери `n` и `m` ще наричаме вектор с размер `m`, от вектори с размер `n`, или с други думи:
```agda
Matrix : Set -> Nat -> Nat -> Set
Matrix A n m = Vector (Vector A n) m
```

Имплементирайте транспониране на матрици:
```agda
-- vpure and vmap could be useful here
transpose : {A : Set} {n m : Nat} -> Matrix A n m -> Matrix A m n
```

Докажете че "транспонирането два пъти" на една матрица не я променя:
```agda
transpose-transpose-id : {A : Set} {n m : Nat} (xss : Matrix A n m) -> transpose (transpose xss) == xss
```
