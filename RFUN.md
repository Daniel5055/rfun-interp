# RFUN

1. **Pure** : Functions do not contain side-effects, no dependence on external state
---
2. **Functional** : Programs made from composing and applying functions
---
3. **Reversable** : Functions can be 'uncalled' with their outputs to give their inputs
---
4. **Programming Language** : To create programs. Syntax used ressembles Haskell
---

## How the Syntax ressembles Haskell

```haskell
-- Natural numbers as Peano numbers

-- Z = 0
-- S Z = 0 + 1 = 1
-- S (S Z) = 0 + 1 + 1 = 2
-- S (S (S Z)) = 0 + 1 + 1 + 1 = 3

data Nat = Z | S Nat

-- Addition of Natural numbers
plus :: Nat -> Nat <-> Nat
plus Z     x = x
plus (S y) x =
  let x' = plus y x
  in  (S x')

-- Function returning nth and n-1th fibonnaci numbers
fib :: Nat <-> (Nat, Nat)
fib Z    = ((S Z),Z)
fib (S m) =
  let (x,y) = fib m
      y' = plus x y
  in (y', x)
```

### Like Haskell

- You **can** type type functions *similarly*
- You **can** define algebraic data types
- You **can** pattern match and define let-variables

### Unlike Haskell

- You **cannot** partially apply functions (`(plus 1) 2`)
- You **cannot** define type classes
- You **cannot** use local variables more than once, or less than once (**Linearity**)

## How RFUN is different from Haskell

### Uncalling

- A function can be 'uncalled':

```
minus :: Nat -> Nat <-> Nat
minus y x = plus! y x
```

### Linearity

- Linear type system requires variables to be used exactly once

- Also used in Rust

- When resources consumed exactly once, we can reconstruct their value from where they were consumed

- To duplicate values, there exists predefined data constructors and functions

```haskell
data EQ = Eq | Neq a

eq :: a -> a <-> EQ

-- Define duplication by reversing equality
dup :: a -> () <-> a
dup x () =  eq! x Eq
```

### Ancillary Variables

```haskell
plus :: Nat -> Nat <-> Nat
            ^       ^
            |   Reversible
            |
        The ancilary
```

```haskell
plus 1 3 == plus 3 1 == 4

plus! 4 == ?????
```

```haskell
plus :: (Nat, Nat) -> (Nat, Nat)

plus (1, 3) == (1, 4)
plus (3, 1) == (3, 1)

plus! (1, 4) == (1, 3)
```

- Ancillary variables are syntactic sugar

- Representing variables that are unchanged over function call (or reconstructed)

- For linearity, ancillary arguments are not consumed

### First Match Policy

- Results of a function must not be the result of any previous branches, regardless of variable values

- Applies for multiple function definitions and case statements for example

- A failing example: 

```haskell
decrement :: Nat <-> Nat
decrement (S y) = y

increment x = S x
```

- If `f Z = Z` then `f! Z = Z`
- But above example gives `f! Z = S Z` as it violates FMP

## More

```haskell
mult :: Nat -> Nat <-> Nat
mult x     Z    = Z
mult x (S  y) =
  let m = mult x y
  in  plus x m

data Bool = True | False

even :: Nat -> () <-> Bool
even 0 () = True
even 1 () = False
even (S y) () =
  let b = even y ()
  in not b

not :: Bool <-> Bool
not True = False
not False = True


map :: (a <-> b) -> [a] <-> [b]
map fun [] = []
map fun (l:ls) =
  let l' = fun l
      ls' = map fun ls
  in  (l':ls')

-- Equal to the Haskell tails function
tails :: [a] <-> [[a]]
tails [] = [[]]
tails (x:xs) =
  let xs' = dup xs ()
      ys = tails xs
  in  ((x:xs'):ys)

scanl1 :: (a -> a <-> a) -> [a] <-> [a]
scanl1 fun []  = []
scanl1 fun [x] = [x]
scanl1 fun (x:y:ls) =
    let y' = fun x y
        ls' = scanl1 fun (y':ls)
    in  (x:ls')

scanr1 :: (a -> a <-> a) -> [a] <-> [a]
scanr1 fun []  = []
scanr1 fun [x] =[x]
scanr1 fun (x:y:ls) =
  let (y':ls') = scanr1 fun (y:ls)
      x' = fun y' x
  in  (x':y':ls')

---------------------------------------------------------------
---- APPLICATIONS
---------------------------------------------------------------

-- The implementation of a run-length encoding function
-- using the equality function
pack :: [a] <-> [(a, Nat)]
pack [] = []
pack (c1 : r) =
  case (pack r) of
    [] -> [(c1, 1)]
    ((c2, n) : t) ->
      case (eq c1 c2) of
        (Neq c2p) -> ((c1, 1) : (c2p, n) : t)
        (Eq) -> ((c1, (S n)) : t)

-- Identical to Haskell group function 
--   and not far from the run-length encoding
group :: [a] <-> [[a]]
group [] = []
group (x:xs) =
  case (group xs) of
    [] -> [[x]]
    ((y:ys):tail) ->
      case (eq x y) of
        (Eq) ->
          let y' = dup x ()
          in  ((x:y:ys):tail)
        (Neq y') -> ([x]:(y':ys):tail)


```







