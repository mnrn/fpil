def hello := "Hello"

def lean : String := "Lean"

#eval String.append hello (String.append " " lean)

def add1 (n : Nat) : Nat := n + 1

#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then k else n

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

#eval maximum (5 + 8) (2 * 7)

-- exercises begin

def joinStringWith (a : String) (b : String) (c : String) : String :=
  String.append b (String.append a c)

#eval joinStringWith ", " "one" "and another"

#check joinStringWith

def volume(height width depth : Nat) : Nat :=
  height * width * depth

#eval volume 2 3 4

--exercises end

def Str : Type := String

def aStr : Str := "This is a string"

def NaturalNumber : Type := Nat

def thirtyEight: NaturalNumber := (38 : Nat)

abbrev N : Type := Nat

def thirtyNine : N := 39
