{-# OPTIONS --no-unicode #-} -- turn off automatic unicode insertion

module 02-agda-start where

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

-- a haskell type declaration
--data List a
--  = Nil
--  | Cons a (List a)
--

-- same thing but in agda
--data List (A : Set) : Set where
--  Nil : List A
--  Cons : A -> List A -> List A

-- X : Y - "X is of type Y"
-- Set is the "kind" of types
-- it's safe to just read it as "Type" instead

-- identity function, with an explicit type as an argument
-- in agda we don't have (and don't need) "implicit polymorphic types"
-- like how in haskell when we write a -> a we actually mean "for all a (a -> a)"
-- so instead we "simulate" it by taking a type as an argument
id' : (A : Set) -> A -> A
id' _ x = x

-- we can also have it implicitly inferred, by using {} to specify the argument
-- agda doesn't have global type inference (because it's not decidable in general) - you always need to write top level signatures
id : {A : Set} -> A -> A
id x = x

-- a data type definition
-- it has no constructors
-- therefore it cannot be constructed!
-- this is an encoding of "falsity" exactly because you can't make values (proofs) of it
-- called Zero because it contains 0 values
data Zero : Set where -- ⊥

-- therefore if you are handed something of Zero
-- you can try to inspect it, to show that it's not possible for it to exist!
-- this is "efq"
naughtE : {A : Set} -> Zero -> A
naughtE ()
--      ^ this bit is special syntax for "impossible case" - not the same thing as () in haskell

-- a record type - "dual" in some sense to a data type
-- very similar to a struct in C:
-- in order to construct a record type, you need to give values for all its fields
-- this record has *no* fields, therefore to construct it you need to give *no values*
-- and it is therefore very easy to construct
-- it encodes "trivial truth" in logic, exactly because you don't need any assumptions to create it
-- the "constructor <>" syntax introduces a convenient way to create values from this type, instead of using record syntax
-- called One because it contains one value
record One : Set where -- unit/top/⊤
  constructor <>

-- an example value from One
one : One
one = <>

-- an example value constructed with record syntax
one' : One
one' = record {} -- no values to give!

-- example of a record type with some actual fields!
--record Student : Set where
--  field
--    fn : Number -- these types don't actually exist yet, but let's assume they do
--    name : String
--
--georgi : Student
--georgi =
--  record
--    { fn = {!81248!}
--    ; name = {!"Georgi"!}
--    }


-- boolean values - to construct a Two we either use the ff or the tt constructor
-- called Two because it has two values
data Two : Set where
  ff : Two
  tt : Two

-- an example of "mixfix" syntax
-- we can define a function with three arguments
-- the _s are where we would place arguments
if_then_else_ : {A : Set} -> Two -> A -> A -> A
if ff then t else e = e
if tt then t else e = t

-- we can write ordinary functions that return types, based on some value!
-- this function "promotes" the boolean *values* to their "corresponding" *logical types*
-- e.g. we convert the boolean "false" to our encoding of falsity - the type Zero
IsTrue : Two -> Set
IsTrue ff = Zero
IsTrue tt = One

_ : IsTrue tt
_ = <>

-- a sum type - it's either the left thing or the right thing
-- Either in haskell
-- as a logical construction it's a proof of either a or either b
data _+_ (A B : Set) : Set where -- A || B
  inl : A -> A + B
  inr : B -> A + B

_ : Zero + One
_ = inr <>

-- two-tuples defined as a record
-- a logical encoding for proof of *both* a *and* b
-- (a, b) in haskell
-- we will instead get this as a special case from our next construction
--record _*_ (A B : Set) : Set where -- A && B
--  constructor _,_
--  field
--    fst : A
--    snd : B

-- a **dependent two-tuple** - called a sigma type in books
-- **the type of the second field can depend on the value of the first**
-- this is an encoding of "exists" quantifiers-
-- to prove (constructively) ∃x.P(x), you must give me a x₀, and then prove that P(x₀)
-- which is effectively a two-tuple of a value x, and a proof P x
record _><_ (A : Set) (P : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : P fst

infixr 15 _><_
open _><_

-- an example of a dependent tuple
-- we give a value, and then show proof that the value satisfies our predicate "IsTrue"
-- ofcourse, if we give the value ff, we would not be able to construct this, because we cannot prove Zero
_ : Two >< IsTrue
_ = tt , <>

-- another example of construction of a sigma type
--data Nat : Set where
--  zero : Nat
--  suc : Nat -> Nat
--
--three : Nat
--three = suc (suc (suc zero))
--
--Even : Nat -> Set
--Even zero = One
--Even (suc zero) = Zero
--Even (suc (suc x)) = Even x
--
--twoIsEven : Nat >< Even
--twoIsEven = (suc (suc zero)) , <>

-- and now we can get our regular 2-tuples for free as a special case of sigma types
-- in which the second argument doesn't depend on the first (notice how our lambda ignores its argument)
_*_ : (A B : Set) -> Set
A * B = A >< \_ -> B
infixr 15 _*_

-- we can encode Either using a sigma type with Two as our left type!
-- to construct an Either
-- you must either use tt (the "left" constructor) in which case our if then else will compute to A, therefore we must give an A
-- or you must either use ff (the "right" constructor) in which case our if then else will compute to B, therefore we must give a B
Either : (A B : Set) -> Set
Either A B = Two >< \b -> if b then A else' B
  where
  -- note: I used another version of if_then_else, because our original one had arguments that are **values of some type**, i.e. (x : A), for some A : Set,
  -- but here we're actually using the **A itself** as an argument, and our original function handle this
  -- this one is **polymorphic over levels** (similar to kind polymorphism in haskell) - it works for both (x : A) and for (A : Set) and for a lot of other stuff
  if_then_else'_ : forall {l} -> {A : Set l} -> Two -> A -> A -> A
  if ff then t else' e = e
  if tt then t else' e = t


-- an example of a function using _*_
-- and a theorem at the same time
-- if you know that A * B is true, then you can also prove B * A (so some kind of symmetry/commutativity)
*-theorem1 : {A B : Set} -> A * B -> B * A
*-theorem1 (x , y) = y , x


-- peano-encoded natural numbers
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat -- a recursive case in a constructor
{-# BUILTIN NATURAL Nat #-} -- pragma allows us to write literals, e.g. 2 to mean (suc (suc zero)), and also to compile these to Integer, if we compile to haskell

-- traditional left-recursive peano nat addition
-- how you define your functions has great repercussions!
-- because all your proofs will now have to look at the left argument of n +N m in order to proceed!
_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

infixr 30 _+N_

-- an equality type
-- to show that x == y for some values x and y
-- you can do only one thing: show that x and y are actually the same value (by using the refl constructor)
-- this "syntactic equality" is internal to agda, but you can think of it as basically "the same structure" (when you look at e.g. constructors)
data _==_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x == x

infix 20 _==_
{-# BUILTIN EQUALITY _==_ #-} -- allows us to use rewrites for this equality type


-- a proof that 2 is equal to 2
-- since 2 is the same syntactic object (suc (suc zero)) as itself, we can use refl
twoIsTwo : 2 == 2
twoIsTwo = refl

-- similarly, in this case 1 +N 1 is not immediately the same thing as 2
-- but agda automatically applies (beta-reduces) the definition of +N as much as possible,
-- and can calculate that they are actually the same!
onePlusOneIsTwo : (1 +N 1) == 2
onePlusOneIsTwo = refl

-- another way to define == where the x is a parameter instead
--data _=='_ {A : Set} (x : A) -> A -> Set where
--  refl : x == x

-- a proof demonstrating how to use ==
-- this states that if you have two proofs of x and y being equal
-- then the proofs themselves are equal to one another!
==-unique : {A : Set} {x y : A} (p1 p2 : x == y) -> p1 == p2
==-unique refl refl = refl
-- note that this is not always true, and it is an active area of research (homotopy type theory),
-- which might provide solutions to problems in constructive mathematics
-- in it, you cannot prove this theorem, and indeed, there are p1 and p2 there, which *are not* equal to each other

-- ap allows us to "apply a function to both sides of an equality"
-- i.e. on a piece of paper we automatically assume this, because f is a function
ap : {A B : Set} {x y : A} (f : A -> B) -> x == y -> f x == f y
ap f refl = refl

-- this proof doesn't need to look at n at all, because we have a case for 0 +N _ in the definition of +N
-- and agda can automatically compute it
+N-left-zero : (n : Nat) -> 0 +N n == n
+N-left-zero n = refl

-- but it is not the same in this case!
-- and thus we use recursion to prove this
+N-right-zero : (n : Nat) -> n +N 0 == n
+N-right-zero zero = refl
+N-right-zero (suc n') = ap suc (+N-right-zero n')
-- another alternative to the last case would be to use "rewrite"
-- the rewrite declaration allows us to "rewrite" our goal by using an equality provided by us
-- i.e. if we have a goal that has some x's in it, and we have a proof (p : x == y)
-- then rewrite p will change all the x's into y's in our goal

+N-assoc : (n m k : Nat) -> (n +N m) +N k == n +N (m +N k)
+N-assoc zero m k = refl
+N-assoc (suc n) m k rewrite +N-assoc n m k = refl

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

data _<=_ : Nat -> Nat -> Set where
  ozero : {n : Nat} -> zero <= n
  osuc : {n m : Nat} -> n <= m -> suc n <= suc m

-- TODO: show some inequalities

---- EXERCISE: <=-refl
--<=-refl : (n : Nat) -> n <= n
--<=-refl n = ?
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
---- _+V_ : ?
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
