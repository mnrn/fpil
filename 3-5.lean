#check 2 < 4

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat

instance : LE Pos where
  le x y := LE.le x.toNat y.toNat

def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp

def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf => true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ => false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def treeA : BinTree Nat := .branch .leaf 10 .leaf
def treeB : BinTree Nat := .branch .leaf 10 .leaf
def treeC : BinTree Nat := .branch .leaf 20 .leaf

#eval treeA == treeB
#eval treeA == treeC
#eval treeA == .leaf

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf => 0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}


deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList

class HAppend' (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider"]

structure PPoint (α : Type) where
  x : α
  y : α

instance : Functor PPoint where
  map f p := { x:= f p.x, y := f p.y }

def concat [Append α] (xs :NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

class Functor' (f : Type → Type) where
  map : { α β : Type } → (α → β) → f α → f β
  mapConst { α β : Type } (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll

-- exercises

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend
    | [], ys => ys
    | (x :: xs), ys => { head := x, tail := xs ++ [ys.head] ++ ys.tail }

#eval  ["Trapdoor Spider"] ++ idahoSpiders
#eval ([] : List String) ++ idahoSpiders
#eval  ["Trapdoor Spider", "Sydney Funnel-web Spider", "Darwin's Bark Spider"] ++ idahoSpiders

def mapBinTree { α β : Type } : (α → β) → BinTree α → BinTree β
  | _, .leaf => .leaf
  | f, .branch l x r => .branch (mapBinTree f l) (f x) (mapBinTree f r)

instance : Functor BinTree where
  map := mapBinTree

#eval (fun x => x ^ 2) <$> treeA
