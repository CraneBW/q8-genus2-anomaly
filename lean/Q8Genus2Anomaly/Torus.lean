import Q8Genus2Anomaly.Cocycle

namespace Q8Genus2Anomaly

def powG (g : Dic n) : Nat → Dic n
  | 0 => one n
  | k+1 => mul (powG g k) g

abbrev Matrix4 := Fin 4 × Fin 4 × Fin 4 × Fin 4
abbrev TorusPair := Q8 × Q8

def determinant (m : Matrix4) : Int :=
  (m.1.val : Int)*m.2.2.2.val - (m.2.1.val : Int)*m.2.2.1.val

def matrices4 : List Matrix4 :=
  ((List.finRange 4).flatMap fun a => (List.finRange 4).flatMap fun b =>
    (List.finRange 4).flatMap fun c => (List.finRange 4).map fun d => (a,b,c,d)).filter
      fun m => decide (determinant m % 4 = 1)

def commutingPairs : List TorusPair :=
  (q8Elements.flatMap fun a => q8Elements.map fun b => (a,b)).filter
    fun (a,b) => decide (mul a b = mul b a)

def acts (m : Matrix4) (a b : Q8) : TorusPair :=
  (mul (powG a m.1.val) (powG b m.2.2.1.val),
   mul (powG a m.2.1.val) (powG b m.2.2.2.val))

def conjugate (t a : Q8) : Q8 := mul (mul t a) (inv t)

def closes (m : Matrix4) (pair : TorusPair) (t : Q8) : Bool :=
  decide (acts m pair.1 pair.2 = (conjugate t pair.1, conjugate t pair.2))

def liftDifference (m : Matrix4) (a b : Q8) : Int × Int :=
  (((m.1.val : Int)-1)*x a + m.2.2.1.val*x b,
   m.2.1.val*x a + ((m.2.2.2.val : Int)-1)*x b)

def halfPairing (u v y₁ y₂ : Int) : Int := (u/2)*y₂ - (v/2)*y₁

def halfDifference (m : Matrix4) (a b : Q8) : Int :=
  let (u,v) := liftDifference m a b
  halfPairing u v (y a) (y b)

def evenLift (m : Matrix4) (a b : Q8) : Prop :=
  (liftDifference m a b).1 % 2 = 0 ∧ (liftDifference m a b).2 % 2 = 0

instance (m : Matrix4) (a b : Q8) : Decidable (evenLift m a b) :=
  inferInstanceAs (Decidable (_ % 2 = 0 ∧ _ % 2 = 0))

def matrixCheck (m : Matrix4) : Bool :=
  commutingPairs.all fun (a,b) => q8Elements.all fun t =>
    if closes m (a,b) t then decide (evenLift m a b ∧ halfDifference m a b % 2 = 0)
    else true

def validCount (m : Matrix4) : Nat :=
  (commutingPairs.map fun pair => (q8Elements.filter (closes m pair)).length).sum

theorem q8_torus_cardinalities :
    matrices4.length = 48 ∧ commutingPairs.length = 40 ∧ q8Elements.length = 8 := by
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem q8_torus_1920 : (matrices4.map validCount).sum = 1920 := by
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem q8_torus_exhaustive : matrices4.all matrixCheck = true := by
  decide

theorem mem_matrices4 (m : Matrix4) (valid : determinant m % 4 = 1) : m ∈ matrices4 := by
  rcases m with ⟨a,b,c,d⟩
  simp [matrices4, valid]

theorem mem_commutingPairs (a b : Q8) (commute : mul a b = mul b a) :
    (a,b) ∈ commutingPairs := by
  simp [commutingPairs, commute, mem_q8Elements]

/-- The parity of the Bockstein/Wang half-difference pairing vanishes on every
    valid finite torus configuration, including arbitrary time holonomy. -/
theorem q8_torus_blind (m : Matrix4) (a b t : Q8)
    (det : determinant m % 4 = 1) (commute : mul a b = mul b a)
    (stabilizes : acts m a b = (conjugate t a, conjugate t b)) :
    evenLift m a b ∧ halfDifference m a b % 2 = 0 := by
  have hm := List.all_eq_true.mp q8_torus_exhaustive m (mem_matrices4 m det)
  unfold matrixCheck at hm
  have hp := List.all_eq_true.mp hm (a,b) (mem_commutingPairs a b commute)
  have ht := List.all_eq_true.mp hp t (mem_q8Elements t)
  simp [closes, stabilizes] at ht
  exact ht

/-- Changing the integral lift of the SL₂(Z/4) matrix has no effect modulo two. -/
theorem halfDifference_lift (u v k l : Int) (a b : Q8) :
    halfPairing (u+4*k) (v+4*l) (y a) (y b) % 2 =
      halfPairing u v (y a) (y b) % 2 := by
  rcases y_bit a with ha | ha <;> rcases y_bit b with hb | hb <;>
    simp [halfPairing, ha, hb] <;> omega

end Q8Genus2Anomaly
