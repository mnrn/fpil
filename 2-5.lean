def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5


def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7

def test : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"

#eval test

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 5

#eval from5.length

def runActions : List (IO Unit) → (IO Unit)
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

#eval runActions (countdown 3)
