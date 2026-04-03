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

instance : ToString Pos where
  toString x := toString (x.toNat)

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)

--class HPlus (α : Type) (β : Type) (γ : Type) where
--  hPlus : α → β → γ

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)

#eval HPlus.hPlus (3 : Pos) (5 : Nat)

--instance [Add α] : HPlus α α α where
--  hPlus := Add.add

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#eval HPlus.hPlus (3 : Nat) (5 : Nat)

#check HPlus.hPlus (5 : Nat) (3 : Nat)

#check HPlus.hPlus (5 : Nat)

structure PPoint (α : Type) where
  x : α
  y : α

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p s := { x := p.x * s, y := p.y * s }

#eval { x := 2.5, y := 3.7 : PPoint Float } * 2.0
