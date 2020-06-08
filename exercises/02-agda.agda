{-# OPTIONS --no-unicode #-} -- turn off automatic unicode insertion

module 02-agda where

-------------------------------------------------------------------------------------------------------
-- ADDITIONAL RESOURCES |
-------------------------
-- допълнителни ресурси:
-- https://github.com/pigworker/CS410-17 - курс (има и домашни) с видео лекции, добър лектор
-- ^ има още много repo-та които си струват разглеждане
-- един от хората измислили Applicative бтв, както и with-abstraction, което ще видим по-късно

-- https://plfa.github.io/ - книга с подробни обяснения и описания, има и упражнения, втората част се занимава с имплементиране на ламбда смятане

-------------------------------------------------------------------------------------------------------
-- CHEATSHEETS |
----------------
-- SPACEMACS CHEATSHEET:
-- <SPC> h <SPC> -- search for help, including agda's help

-- <SPC> <TAB> - go to previous buffer -- helpful to go back after looking at help
-- <SPC> z x -/= - decrease/increase font size

-- normal emacs agda bindings:
-- https://agda.readthedocs.io/en/v2.6.1/tools/emacs-mode.html#keybindings
-- spacemacs agda layer bindings (but also can open them with <SPC> h <SPC> inside spacemacs):
-- https://github.com/syl20bnr/spacemacs/tree/master/layers/%2Blang/agda#key-bindings

-- AGDA CHEATSHEET (descending importance):
-- <SPC> m l - reload file

-- <SPC> m , - (in goal) show context and goal

-- <SPC> m . - (in goal) show type of expression in goal. if goal is empty agda will ask for an expression to type

-- <SPC> m c - case split on goal contents
--             if goal is empty, will ask for what to split on

-- <SPC> m r - introduce constructor (if non-ambiguous)
--             can also introduce constructors, lambdas, record constructors
--             if there's a function in the goal it will "introduce" it with its arguments as new goals

-- <SPC> m <SPC> - when in a goal, replace the goal with the expression currently in the goal
--               if the goal is empty, agda will ask for an expression to insert
--               obviously only works if types match

-- <SPC> m a - (invoke "agsy") agda try your best to figure this out!
--             you can add names to a goal to give hints to agda, e.g. if you want to use a function "f"

-- <SPC> m x r - restart agda

-- <SPC> u <SPC> u <other-command> - kindly ask agda to evaluate and desugar everything as much as it can when executing <other-command>

-- <SPC> m f - go to next goal

-- <SPC> m n - compute an expression

-- <SPC> m h - when in a hole, compute what the type of a helper function you need here would be

-------------------------------------------------------------------------------------------------------
-- EXERCISE |
-------------

-- TODO: id
-- show function example - id
-- mention always needing to write types!

-- TODO: implicit id
-- show implicit arguments for id

-- TODO: Zero
-- define Zero
-- explain data
-- single colon!
-- what is Set?
-- propositions as types
-- falsity encoding - as usual, reminder

-- TODO: naughtE
-- efq
-- I can produce anything if you give me something that doesn't exist
-- if you're lying, I can also lie

-- TODO: One
-- define One
-- explain record
-- mention records have better inference! (eta-equality by default)
-- with constructor <>

-- TODO: Two
-- define Two to show sum types
-- show mixfix syntax with if then else

-- TODO: IsTrue
-- show calculating types via IsTrue
-- "lifting" bools to proofs/types

-- TODO:
-- define _+_
-- can write multiple things of the same type within one set of brackets

-- TODO:
-- define _*_ to show a record with fields, and the immediately hide it

-- TODO:
-- define sigma _><_, talk about dependent products
-- infixr 15 _><_

-- open _><_

-- TODO: show sigma example
-- <SPC> m r - introduce constructor
-- <SPC> m a - auto
-- ttIsTrue : Two >< IsTrue

-- TODO:
-- define _*_ as non-dependent sigma
-- _*_ : (A B : Set) -> Set
-- infixr 15 _*_

-- TODO: *-comm
-- commutativity - but also swap!
-- <SPC> m c - case split

-- TODO: Nat
-- define Nat - recursive
-- {-# BUILTIN NATURAL Nat #-}

-- TODO: nat addition
-- show _+N_, mention spaces are important! (it's +N because we're going to have other such things)
-- _+N_ : Nat -> Nat -> Nat

-- infixr 30 _+N_

-- TODO:
-- define _==_ -- explanations holy! this is confusing!
-- wordplay? what does it mean "to be the same" - syntactic equality

-- with indices
-- infix 20 _==_
-- {-# BUILTIN EQUALITY _==_ #-}

-- also with parameter

-- TODO: uniqueness of ==
-- mention this isn't always true (homotopy type theory)!
-- ==-unique : {A : Set} {x y : A} (p1 p2 : x == y) -> p1 == p2

-- TODO: ap, but after +N-right-zero
-- ap : {A B : Set} {x y : A} (f : A -> B) -> x == y -> f x == f y

-- TODO:
-- show +N-left-zero
-- +N-left-zero : (n : Nat) -> 0 +N n == n

-- TODO:
-- show right-zero -- talk about STUCKNESS!!!
-- ap for eq! show it step by step! and show how to check recursive call with <SPC> m .
-- +N-right-zero : (n : Nat) -> n +N 0 == n

-- TODO: show proof assoc
-- show rewrite
-- +N-assoc : (n m k : Nat) -> (n +N m) +N k == n +N (m +N k)
-- we just proved +N with 0 is a monoid!

-- TODO:
-- define _<=_

-- TODO: show some inequalities

-- TODO: _<=_ reflexivity
-- <=-refl : (n : Nat) -> n <= n

---- EXERCISES ==
--
---- EXERCISE: == is symmetric
--==-symm : {A : Set} {x y : A} -> x == y -> y == x
--==-symm = ?
--
---- EXERCISE: == is transitive
--==-trans : {A : Set} {x y z : A} -> x == y -> y == z -> x == z
--==-trans = ?
--
---- EXERCISES Nats
--
---- EXERCISE: suc is injective
--suc-inj : {n m : Nat} -> suc n == suc m -> n == m
--suc-inj = ?
--
---- EXERCISE: <=-trans
--<=-trans : {n m k : Nat} -> n <= m -> m <= k -> n <= k
--<=-trans = ?
--
---- EXERCISE: suc n is not less than or equal to n
--suc-suc-not-<= : {n : Nat} -> suc n <= n -> Zero
--suc-suc-not-<= = ?
--
---- EXERCISE: <= proofs are unique
---- use ap or rewrite!
--<=-unique : {n m : Nat} -> (p1 p2 : n <= m) -> p1 == p2
--<=-unique = ?
--
---- lists
--
--data List (A : Set) : Set where
--  [] : List A
--  _,-_ : A -> List A -> List A
--
--infixr 50 _,-_
--
---- EXERCISE:
---- Define list appending
---- HINT: look at +N if you haven't done this before
--_+L_ : {A : Set} -> List A -> List A -> List A
--xs +L ys = ?
--
--infixr 30 _+L_
--
---- EXERCISE:
---- +L is a monoid - with what left and right unit?
---- i.e. for what x is it true that for any xs:
---- x +L xs == xs and xs +L x == xs
---- TODO: delete []
--+L-left-id : {A : Set} (xs : List A) -> [] +L xs == xs
--+L-left-id = ?
--
--+L-right-id : {A : Set} (xs : List A) -> xs +L [] == xs
--+L-right-id = ?
--
---- EXERCISE:
---- +L is associative
---- HINT: look at +N-assoc
--+L-assoc : {A : Set} (xs ys zs : List A) -> (xs +L ys) +L zs == xs +L (ys +L zs)
--+L-assoc = ?
--
---- EXERCISE: list map
---- define map for lists - apply a function to every argument
--map : {A B : Set} -> (A -> B) -> List A -> List B
--map = ?
--
---- EXERICSE: mapping id is the same as just id
--map-id-is-id : {A : Set} -> (xs : List A) -> map id xs == xs
--map-id-is-id = ?
---- Note: we apply the argument to avoid extensionality issues
--
---- left-to-right composition
--_<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
--(f << g) x = ?
--
---- EXERCISE: mapping a composition is the same as composing mappings
---- <SPC> u <SPC> u <other-command>
---- might be useful here
--map-compose : {A B C : Set} (f : B -> C) (g : A -> B) (xs : List A) -> map (f << g) xs == (map f << map g) xs
--map-compose = ?
--
---- EXERCISE: mapping after appending is the same as first mapping and then appending
--map-distrib-+L : {A B : Set} (f : A -> B) (xs ys : List A) -> map f (xs +L ys) == map f xs +L map f ys
--map-distrib-+L = ?
--
---- EXERCISE: length-indexed lists - vectors
---- "lists that know their length"
--
--data Vector (A : Set) : Nat -> Set where
--  [] : Vector A zero -- the empty vector has a length of 0
--  _,-_ : {n : Nat} -> A -> Vector A n -> Vector A (suc n) -- if we cons an element to a vector of length n, we get a vector of length (suc n)
--
---- EXERCISE: We can now define a safe head and tail - you can't call them with []
---- Compare this to the default ones in haskell, that can throw exceptions
--vhead : {A : Set} {n : Nat} -> Vector A (suc n) -> A
--vhead = ?
--
--vtail : {A : Set} {n : Nat} -> Vector A (suc n) -> Vector A n
--vtail = ?
--
---- EXERCISE: We can also define "safe" take, that does not "overshoot"
---- Note how we don't need to pass n explicitly, because n <= m holds this information already
--vtake : {A : Set} {n m : Nat} -> n <= m -> Vector A m -> Vector A n
--vtake = ?
--
---- EXERCISE: Our zip is also "safe" in that we don't lose any information from either vector
--vzip : {A B : Set} {n : Nat} -> Vector A n -> Vector B n -> Vector (A * B) n
--vzip = ?
--
---- EXERCISE: Append vectors
---- What type should this function have?
---- _V+_ : ?
--
---- EXERCISE: We can split a vector if we know its size is a sum of two numbers
---- N.B.! you need to pattern match on the left number here, because otherwise agda doesn't know
---- what cases could be possible for the vector
--vsplit : {A : Set} (n m : Nat) -> Vector A (n +N m) -> Vector A n * Vector A m
--vsplit = ?
--
---- EXERCISE: Appending two vectors and then splitting them should yield the original two vectors!
---- What type should this have?
---- vsplit-+V-id : ?
--
---- EXERCISE: you can also suc on the right in +N
--+N-right-suc : (n m : Nat) -> suc (n +N m) == n +N suc m
--+N-right-suc = ?
--
---- EXERCISE: +N is commutative
---- prove lemmas if something seems too hard!
---- you'll need to prove a lemma for the recursive case
---- HINT:
---- use ==-symm and +N-right-zero in the base case
---- and +N-right-suc in the recursive case (+ rewrite or ap + ==-trans)
--+N-commut : (n m : Nat) -> n +N m == m +N n
--+N-commut = ?
--
---- EXERCISE: multiplication
---- use addition
--_*N_ : Nat -> Nat -> Nat
--n *N m = ?
--infixr 40 _*N_
--
---- EXERCISE: multiplication right identity
--*N-right-id : (n : Nat) -> n *N 1 == n
--*N-right-id = ?
--
---- EXERCISE: multiplication distributes over addition
---- HINT: use rewrite and ==-symm + +N-assoc in the recursive case
--*N-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
--*N-distrib-+N = ?
--
---- EXERCISE: multiplication is associative
---- HINT: user *N-+N-distrib and rewrite
--*N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
--*N-assoc = ?
