import Q8Genus2Anomaly.Group

namespace Q8Genus2Anomaly

def omegaEven (a b c : Dic n) : Int := x a * x b * y c
def carry (a b : Int) : Int := (a+b)/4
def omegaOdd (a b c : Dic n) : Int := (q a % 2) * carry (q b) (q c)

def delta (f : Dic n → Dic n → Dic n → Int) (a b c d : Dic n) : Int :=
  f b c d - f (mul a b) c d + f a (mul b c) d - f a b (mul c d) + f a b c

def Normalized (f : Dic n → Dic n → Dic n → Int) : Prop :=
  ∀ a b, f (one n) a b = 0 ∧ f a (one n) b = 0 ∧ f a b (one n) = 0

theorem even_normalized (n : Nat) : Normalized (n := n) omegaEven := by
  intro a b
  simp [omegaEven, one]

theorem q_nonneg (a : Dic n) : 0 ≤ q a := Int.emod_nonneg _ (by decide)
theorem q_lt (a : Dic n) : q a < 4 := Int.emod_lt_of_pos _ (by decide)

theorem odd_normalized (n : Nat) : Normalized (n := n) omegaOdd := by
  intro a b
  have hb : q b / 4 = 0 := by have := q_nonneg b; have := q_lt b; omega
  simp [omegaOdd, one, carry, hb]

theorem y_bit (a : Dic n) : y a = 0 ∨ y a = 1 := by
  cases h : a.2 <;> simp [y, h]

private theorem cup3_arithmetic (a b c e f : Int)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (he : e = 0 ∨ e = 1) (hf : f = 0 ∨ f = 1) :
    (b*c*f - ((a+b)%2)*c*f + a*((b+c)%2)*f - a*b*((e+f)%2) + a*b*e) % 2 = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases he with rfl | rfl <;>
    rcases hf with rfl | rfl <;> decide

theorem even_cocycle (even : half n % 2 = 0) (a b c d : Dic n) :
    delta omegaEven a b c d % 2 = 0 := by
  simp only [delta, omegaEven, x_mul even, y_mul]
  exact cup3_arithmetic (x a) (x b) (x c) (y c) (y d)
    (Int.emod_two_eq _) (Int.emod_two_eq _) (Int.emod_two_eq _) (y_bit c) (y_bit d)

theorem carry_cocycle (a b c : Int) :
    carry b c - carry ((a+b)%4) c + carry a ((b+c)%4) - carry a b = 0 := by
  unfold carry
  omega

theorem odd_cocycle (odd : half n % 2 = 1) (a b c d : Dic n) :
    delta omegaOdd a b c d % 2 = 0 := by
  simp only [delta, omegaOdd, q_mul odd]
  have h := carry_cocycle (q b) (q c) (q d)
  have parity : ((q a + q b) % 4) % 2 = ((q a % 2) + (q b % 2)) % 2 := by omega
  rw [parity]
  rcases Int.emod_two_eq (q a) with ha | ha <;>
    rcases Int.emod_two_eq (q b) with hb | hb <;>
    rw [ha, hb] <;> simp <;> omega

def q8Elements : List Q8 :=
  (List.finRange 4).flatMap (fun p => [(p,false), (p,true)])

theorem mem_q8Elements (g : Q8) : g ∈ q8Elements := by
  rcases g with ⟨p,b⟩
  cases b <;> simp [q8Elements]

def q8CocycleCheck : Bool :=
  q8Elements.all fun a => q8Elements.all fun b => q8Elements.all fun c =>
    q8Elements.all fun d => decide (delta omegaEven a b c d % 2 = 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem q8_cocycle_4096 : q8Elements.length ^ 4 = 4096 ∧ q8CocycleCheck = true := by
  decide

theorem q8_cocycle_all (a b c d : Q8) : delta omegaEven a b c d % 2 = 0 := by
  have h := q8_cocycle_4096.2
  unfold q8CocycleCheck at h
  rw [List.all_eq_true] at h
  have h := h a (mem_q8Elements a)
  rw [List.all_eq_true] at h
  have h := h b (mem_q8Elements b)
  rw [List.all_eq_true] at h
  have h := h c (mem_q8Elements c)
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h d (mem_q8Elements d))

end Q8Genus2Anomaly
