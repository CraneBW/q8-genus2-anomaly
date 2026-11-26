import Q8Genus2Anomaly.Bar

namespace Q8Genus2Anomaly

abbrev Word := List Int
abbrev WChain2 := List ((Word × Word) × Int)
abbrev WChain3 := List ((Word × Word × Word) × Int)

def inverseWord (w : Word) : Word := w.reverse.map Neg.neg

def reduceWord (w : Word) : Word :=
  (w.foldl (fun acc letter => match acc with
    | head::tail => if head = -letter then tail else letter::acc
    | [] => [letter]) []).reverse

def substitute (images : Array Word) (w : Word) : Word :=
  reduceWord <| w.flatMap fun letter =>
    let image := images[letter.natAbs-1]?.getD []
    if letter < 0 then inverseWord image else image

def relator : Word := [1,2,-1,-2,3,4,-3,-4]
def torusRelator : Word := [1,2,-1,-2]
def seamWord : Word := [2,-1,-2,3]

def twist1 : Array Word := #[[1],[2,1],[3],[4]]
def twist2 : Array Word := #[[1,-2],[2],[3],[4]]
def twist3 : Array Word :=
  #[[1], inverseWord seamWord ++ [2], inverseWord seamWord ++ [3] ++ seamWord, [4] ++ seamWord]
def twist4 : Array Word := #[[1],[2],[3,-4],[4]]
def twist5 : Array Word := #[[1],[2],[3],[4,3]]

def phi : Array Word :=
  (([[1],[2],[3],[4]] : List Word).map fun word =>
    [twist5, twist5, twist3, twist3, twist1, twist1].foldl
      (fun current twist => substitute twist current) word).toArray

def ta4 : Array Word := #[[1],[2,1,1,1,1]]

theorem five_twists_preserve :
    ([twist1,twist2,twist3,twist4,twist5].map fun t => substitute t relator) =
      List.replicate 5 relator := by decide

theorem phi_preserves_R : substitute phi relator = relator := by decide

theorem ta4_preserves_R : substitute ta4 torusRelator = torusRelator := by decide

def wordHolonomy (holonomies : Array (Dic n)) (w : Word) : Dic n :=
  w.foldl (fun current letter =>
    let h := holonomies[letter.natAbs-1]?.getD (one n)
    mul current (if letter < 0 then inv h else h)) (one n)

def rho : Array Q8 := #[r 1, one 1, s 1, one 1]

theorem phi_preserves_rho :
    phi.toList.map (wordHolonomy rho) = rho.toList ∧
      wordHolonomy rho relator = one 1 := by decide

def fiberChain (word : Word) : WChain2 :=
  (word.zipIdx.filterMap fun (letter,j) =>
    if j = 0 then none else some ((word.take j,[letter]),(1 : Int))) ++
  (word.filterMap fun letter =>
    if letter < 0 then some (([letter],[-letter]),-1) else none)

def movedDifference (word : Word) (images : Array Word) : WChain2 :=
  let C := fiberChain word
  (C.map fun ((g,h),c) => ((substitute images g,substitute images h),c)) ++
  (C.map fun (w,c) => (w,-c))

def treeFiller (C : WChain2) : WChain3 :=
  C.flatMap fun ((g,h),c) =>
    h.zipIdx.filterMap fun (letter,j) =>
      let segment := h.take (if letter < 0 then j+1 else j)
      if g.isEmpty || segment.isEmpty then none else
        some ((g,segment,[Int.ofNat letter.natAbs]), if letter < 0 then -c else c)

def freeBoundary (C : WChain3) : WChain2 :=
  C.flatMap fun ((g,h,k),c) =>
    ([((h,k),c), ((reduceWord (g++h),k),-c),
      ((g,reduceWord (h++k)),c), ((g,h),-c)].filter
      (fun ((u,v),_) => !(u.isEmpty || v.isEmpty)))

def addBasis [DecidableEq α] (entry : α × Int) : List (α × Int) → List (α × Int)
  | [] => if entry.2 = 0 then [] else [entry]
  | (b,c)::tail =>
    if b = entry.1 then
      if c + entry.2 = 0 then tail else (b,c + entry.2)::tail
    else (b,c)::addBasis entry tail

def collect [DecidableEq α] (C : List (α × Int)) : List (α × Int) :=
  C.foldl (fun result entry => addBasis entry result) []

def freeMappingChain : WChain3 := treeFiller (movedDifference relator phi)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem free_filler_certificate :
    collect (freeBoundary freeMappingChain ++
      ((movedDifference relator phi).map fun (w,c) => (w,-c))) = [] := by decide

def pushChain (C : WChain3) (hol : Array (Dic n)) : Chain n :=
  collect (C.filterMap fun ((g,h,k),c) =>
    let (a,b,d) := (wordHolonomy hol g,wordHolonomy hol h,wordHolonomy hol k)
    if a = one n ∨ b = one n ∨ d = one n then none else some ((a,b,d),c))

def decodeQ8 (i : Nat) : Q8 := ofInt 1 (i%4 : Nat) (i≥4)
def encodeQ8 (g : Q8) : Nat := g.1.val + if g.2 then 4 else 0

private abbrev Encoded := (Nat × Nat × Nat) × Int

private def tripleIndex (entry : Encoded) : Nat :=
  let (a,b,c) := entry.1
  a*64+b*8+c

private def insertEncoded (entry : Encoded) : List Encoded → List Encoded
  | [] => [entry]
  | head::tail =>
    if tripleIndex entry ≤ tripleIndex head then entry::head::tail
    else head::insertEncoded entry tail

def encodeChain (C : Chain 1) : List ((Nat × Nat × Nat) × Int) :=
  (C.map fun ((a,b,c),k) => ((encodeQ8 a,encodeQ8 b,encodeQ8 c),k)).foldl
    (fun acc entry => insertEncoded entry acc) []

/-- Sorted nonzero coefficients in the ordering (1,i,-1,-i,j,k,-j,-k). -/
def ZAValues : List ((Nat × Nat × Nat) × Int) :=
  [((1,1,1),1), ((1,1,4),-1), ((1,2,1),1), ((1,3,1),1), ((1,6,1),1),
   ((1,6,4),-1), ((4,2,1),-1), ((4,2,4),1), ((4,5,1),-1), ((4,5,4),1),
   ((4,6,4),1), ((6,1,1),-1), ((6,1,4),1), ((6,2,4),-1), ((6,6,1),-1),
   ((6,6,4),1), ((6,7,1),1), ((6,7,4),-1)]

def ZA : Chain 1 :=
  ZAValues.map fun ((a,b,c),k) => ((decodeQ8 a,decodeQ8 b,decodeQ8 c),k)

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
theorem ZA_from_free_filler :
    encodeChain (pushChain freeMappingChain rho) = ZAValues := by decide

def zaBoundaryCheck : Bool :=
  q8Elements.all fun a => q8Elements.all fun b => decide (barBoundary ZA a b = 0)

theorem ZA_cycle : IsCycle ZA := by
  have check : zaBoundaryCheck = true := by decide
  intro a b
  unfold zaBoundaryCheck at check
  rw [List.all_eq_true] at check
  have line := check a (mem_q8Elements a)
  rw [List.all_eq_true] at line
  exact of_decide_eq_true (line b (mem_q8Elements b))

theorem ZA_phase : pairWith ZA omegaEven % 2 = 1 := by decide

end Q8Genus2Anomaly
