def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

-- can be written without {α : Type}:
def length' (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length' ys)

def length'' : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (length'' ys)

def drop : Nat →  List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, _ :: xs => drop n xs

def fromOption (default : α) : Option α → α
  | none => default
  | some x => x

#eval (some "samonberry").getD ""
#eval none.getD ""

#eval fromOption "" (some "samonberry")
#eval fromOption "" none

def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys => (x :: (unzip xys).fst, y :: (unzip xys).snd)

def unzip' : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip' xys
    (x :: unzipped.fst, y :: unzipped.snd)

def unzip'' : List (α × β) → List α × List β
 | [] => ([], [])
 | (x, y) :: xys =>
  let (xs, ys) : List α × List β := unzip'' xys
  (x :: xs, y :: ys)

def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

def unzip''' : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip''' xys
    (x :: unzipped.fst, y :: unzipped.snd)

def unzip'''' (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip'''' xys
    (x :: unzipped.fst, y :: unzipped.snd)

#check 14

#check (14 : Int)

def id' (x : α) : α := x

def id'' (x : α) := x

def drop' (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n, _ :: ys => drop' n ys

def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs', _ :: ys' => sameLength xs' ys'
  | _, _ => false

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

def even' : Nat -> Bool
  | 0 => true
  | n + 1 => not (even' n)

def halve : Nat → Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1

def halve' : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

#eval halve' 15

#eval halve' 42

#check fun x => x + 1

#check fun (x : Int) => x + 1

#check fun {α : Type} (x : α) => x

#check fun
  | 0 => none
  | n + 1 => some n

def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2

#eval double 3

#eval (fun x => x + x) 5

#eval (. * 2) 5

def Nat.double (x : Nat) : Nat := x + x

#eval (4 : Nat).double

namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

#check NewNamespace.triple

#check NewNamespace.quadruple

def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

open NewNamespace in
#check quadruple

inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

def Inline.string? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _ => none

def Inline.string'? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none

structure Point where
  x : Float
  y : Float

#eval (⟨1, 2⟩ : Point)

#eval s!"three five is {NewNamespace.triple 5}"
