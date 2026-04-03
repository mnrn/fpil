#check (IO.println)

#check @IO.println

def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents

def List.sumOfContents' [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents'


def fourNats : List Nat := [1, 2, 3, 4]

#eval fourNats.sumOfContents

structure PPoint (α : Type) where
  x : α
  y : α

instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

inductive Evens : Type where
  | zero : Evens
  | addTwo : Evens → Evens

instance : OfNat Evens  0 where
  ofNat := Evens.zero

instance (n : Nat) [OfNat Evens n] : OfNat Evens (Nat.succ (Nat.succ n)) where
  ofNat := Evens.addTwo (OfNat.ofNat n)
