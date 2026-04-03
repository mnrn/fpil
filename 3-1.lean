inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

#eval Plus.plus 5 3

open Plus (plus)

#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven

#eval fourteen

instance : Add Pos where
  add := Pos.plus

def fourteen' : Pos := seven + seven

#eval fourteen'

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

#eval s!"There are {seven}"

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval [ seven * Pos.one, seven * seven, Pos.succ Pos.one * seven]

instance : One Pos where
  one := Pos.one

#eval (1 : Pos)

inductive LT4 where
  | zero
  | one
  | two
  | three

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)

#eval (0 : LT4)

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8

structure Pos' where
  succ ::
  pred : Nat

def one : Pos' := ⟨0⟩
def two : Pos' := ⟨1⟩

#eval one.pred
#eval two.pred

def Pos'.add (a b : Pos') : Pos' :=
  ⟨a.pred + b.pred + 1⟩

instance : Add Pos' where
  add := Pos'.add

#eval ((⟨0⟩ : Pos') + ⟨1⟩).pred

def Pos'.mul (a b : Pos') : Pos' :=
  ⟨a.pred * b.pred + a.pred + b.pred⟩

instance : Mul Pos' where
  mul := Pos'.mul

#eval ((⟨2⟩ : Pos') * ⟨3⟩).pred

def pos'ToString (p : Pos') : String :=
  s!"{p.pred + 1}"

instance : ToString Pos' where
  toString := pos'ToString

#eval (⟨0⟩ : Pos')

instance : OfNat Pos' (n + 1) where
  ofNat := ⟨n⟩

structure Evens where
  half : Nat

def Evens.add (a b : Evens) : Evens :=
  ⟨a.half + b.half⟩

def Evens.mul (a b : Evens) : Evens :=
  ⟨2 * a.half * b.half⟩

instance : ToString Evens where
  toString n := toString (2 * n.half)

instance : OfNat Evens n where
  ofNat := ⟨n⟩

inductive HttpReq where
  | GET : String → HttpReq
  | POST : String → HttpReq

structure HttpRes where
  status : Nat
  msg : String

instance : ToString HttpRes where
  toString r := s!"{r.status} {r.msg}"
