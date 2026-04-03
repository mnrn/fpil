structure PPoint (α : Type) where
  x : α
  y : α

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check replaceX

#check replaceX Nat

#check replaceX Nat natOrigin

#check replaceX Nat natOrigin 5

#eval replaceX Nat natOrigin 5

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s  with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos

inductive List' (α : Type) where
  | nil : List' α
  | cons : α → List' α → List' α

def primeUnder10 : List Nat := [2, 3, 5, 7]

def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)

#eval length Nat primeUnder10

def length' (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)

#eval length' Nat primeUnder10

def replaceX' { α : Type } (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#eval replaceX' natOrigin 5

def length'' { α : Type } (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length'' ys)

#eval length'' primeUnder10

#eval primeUnder10.length

#check List.length (α := Int)

inductive Option' (α : Type) : Type where
  | none : Option' α
  | some (val : α) : Option' α

def List.head'? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y

#eval primeUnder10.head?

#eval [].head? (α := Int)

#eval ([] : List Int).head?

structure Prod' (α : Type) (β : Type) : Type where
  fst : α
  snd : β

def fives : String × Int := { fst := "five", snd := 5 }
def fives' : String × Int := ("five", 5)

-- Both notations are right-associative. This means that the following definitions are equivalent:
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
def sevens' : String × (Int × Nat) := ("VII", (7, 4 + 3))

inductive Sum' (α : Type) (β : Type) : Type where
  | inl : α → Sum' α β
  | inr : β → Sum' α β

def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals

inductive Unit' : Type where
  | unit : Unit'

inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

inductive WoodSplittingTool where
  | axe
  | maul
  | froe

#eval WoodSplittingTool.axe

def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]

inductive Firewood where
  | birch
  | pine
  | beech
deriving Repr

def allFirewood : List Firewood := [
  Firewood.birch,
  Firewood.pine,
  Firewood.beech
]

#eval allFirewood

def List.tail'? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [y] => some y
  | _ :: ys => List.tail'? ys

#eval allFirewood.tail'?

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | y :: ys =>
    match predicate y with
    | true => some y
    | false => List.findFirst? ys predicate

def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

inductive PetName' where
  | dog : String → PetName'
  | cat : String → PetName'

def animals' : List PetName' :=
  [ PetName'.dog "Spot",
    PetName'.cat "Tiger",
    PetName'.dog "Fifi",
    PetName'.dog "Rex",
    PetName'.cat "Floof"]

def howManyDogs' (pets : List PetName') : Nat :=
  match pets with
  | [] => 0
  | PetName'.dog _ :: morePets => howManyDogs' morePets + 1
  | PetName'.cat _ :: morePets => howManyDogs' morePets

#eval howManyDogs' animals'

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | x :: xs' =>
    match ys with
    | [] => []
    | y :: ys' => (x, y) :: zip xs' ys'

#eval zip allFirewood animals

def zip' : List α → List β → List (α × β)
  | x :: xs', y :: ys' => (x, y) :: zip' xs' ys'
  | _, _ => []

#eval zip' allFirewood animals

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n with
    | Nat.zero => []
    | Nat.succ n' =>
      match xs with
      | [] => []
      | y :: ys => y :: take n' ys

#eval take 3 ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"]

def take' : Nat → List α → List α
  | Nat.succ n, x :: xs => x :: take' n xs
  | _, _  => []

#eval take' 3 ["bolete", "oyster"]
#eval take' 1 ["bolete", "oyster"]

def distributes {α β γ: Type} (p : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match p with
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)

abbrev A := Nat
abbrev B := Bool
abbrev C := String

#eval distributes (α := A) (β := B) (γ := C)
  (1, Sum.inl (true : B))

#eval distributes (α := A) (β := B) (γ := C)
  (2, Sum.inr ("ok"))

def multiplicationByTwo {α : Type} (p : Bool × α) : α ⊕ α :=
  match p with
  | (true, a) => Sum.inl a
  | (false, a) => Sum.inr a

#eval multiplicationByTwo (true,  10)
#eval multiplicationByTwo (false, 10)

#eval multiplicationByTwo (true,  "foo")
#eval multiplicationByTwo (false, "foo")

#eval multiplicationByTwo (true,  (1, true))
#eval multiplicationByTwo (false, (1, true))
