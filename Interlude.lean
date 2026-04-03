def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]

def deer := woodlandCritters[1]

def snail := woodlandCritters[2]

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

def onePlusOneIsTwo' : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo'' : onePlusOneIsTwo' := rfl

theorem onePlusOneIsTwo''' : 1 + 1 = 2 := by
  decide

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem onePlusOneorLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide

theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide

theorem trueIsTrue : True := by decide

theorem trueOrFalse : True ∨ False := by decide

theorem falseImpliesTrue : False → True := by decide

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

#eval third woodlandCritters (by decide)

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters

#eval thirdOption ["only", "two"]

#eval woodlandCritters[1]!

abbrev onePlusOneIsTwo'''' : Prop := 1 + 1 = 2

theorem onePlusOneIsStillTwo : onePlusOneIsTwo'''' := by decide

theorem twoPlusThreeIsFive : 2 + 3 = 5 := rfl

theorem fifteenMinusEightIsSeven : 15 - 8 = 7 := rfl

theorem helloAppendWorldIsHelloWorld : "Hello, ".append "World" = "Hello, World" := rfl

theorem twoPlusThreeIsFive' : 2 + 3 = 5 := by decide

theorem fifteenMunusEightIsSeven' : 15 - 8 = 7 := by decide

theorem helloAppendWorldIsHelloWorld' : "Hello, ".append "World" = "Hello, World" := by decide

theorem fiveLessThanEighteen : 5 < 18 := by decide

def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4]
