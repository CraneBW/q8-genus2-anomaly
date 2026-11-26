import Q8Genus2Anomaly.Cocycle

namespace Q8Genus2Anomaly

abbrev Triple (n : Nat) := Dic n × Dic n × Dic n
abbrev Chain (n : Nat) := List (Triple n × Int)

def pairWith (chain : Chain n) (f : Dic n → Dic n → Dic n → Int) : Int :=
  (chain.map fun ((a,b,c),sign) => sign * f a b c).sum

@[simp] theorem pairWith_nil (f : Dic n → Dic n → Dic n → Int) :
    pairWith [] f = 0 := rfl

@[simp] theorem pairWith_cons (t : Triple n) (c : Int) (C : Chain n)
    (f : Dic n → Dic n → Dic n → Int) :
    pairWith ((t,c)::C) f = c*f t.1 t.2.1 t.2.2 + pairWith C f := rfl

@[simp] theorem pairWith_append (C D : Chain n) (f : Dic n → Dic n → Dic n → Int) :
    pairWith (C ++ D) f = pairWith C f + pairWith D f := by
  simp [pairWith]

/-- Evaluating an integral boundary against a 2-cochain. -/
def barDelta2 (f : Dic n → Dic n → Int) (a b c : Dic n) : Int :=
  f b c - f (mul a b) c + f a (mul b c) - f a b

def indicator2 (p q a b : Dic n) : Int :=
  if a = one n ∨ b = one n then 0 else if a = p ∧ b = q then 1 else 0

def barBoundary (C : Chain n) (p q : Dic n) : Int :=
  pairWith C (barDelta2 (indicator2 p q))

def IsCycle (C : Chain n) : Prop := ∀ p q, barBoundary C p q = 0

/-- The first k summands of D_N, k from 0 to N-1. -/
def rSegment (n : Nat) : Nat → Chain n
  | 0 => []
  | k+1 => ((r n,rpow n (k+1 : Nat),r n),1) :: rSegment n k

def D (n : Nat) : Chain n :=
  rSegment n n ++ [((r n,s n,s n),-1), ((rs n,rs n,r n),-1), ((rs n,r n,s n),-1)]

theorem rSegment_delta (n k : Nat) (f : Dic n → Dic n → Int) :
    pairWith (rSegment n k) (barDelta2 f) =
      f (r n) (rpow n (k+1 : Nat)) - f (rpow n (k+1 : Nat)) (r n) := by
  induction k with
  | zero => simp [rSegment, r]
  | succ k ih =>
    simp only [rSegment, pairWith_cons, Int.one_mul, barDelta2, r_rpow, rpow_r, ih,
      Int.natCast_succ]
    omega

theorem z_rotation (n : Nat) : rpow n (n+1 : Nat) = z n := by
  simp [z, half, Int.natCast_succ]

theorem D_pair_delta (n : Nat) (f : Dic n → Dic n → Int) :
    pairWith (D n) (barDelta2 f) = 0 := by
  simp only [D, pairWith_append, rSegment_delta, z_rotation, pairWith_cons, pairWith_nil,
    barDelta2, r_s, s_s, rs_rs, rs_r]
  omega

theorem D_cycle (n : Nat) : IsCycle (D n) := by
  intro p q
  exact D_pair_delta n (indicator2 p q)

theorem rSegment_even (n k : Nat) : pairWith (rSegment n k) omegaEven = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rSegment, omegaEven, r, rpow, ih]

theorem D_even (n : Nat) : pairWith (D n) omegaEven % 2 = 1 := by
  simp [D, rSegment_even, omegaEven, r, rpow, s, rs]

theorem rSegment_odd (n k : Nat) : pairWith (rSegment n k) omegaOdd = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rSegment, omegaOdd, r, rpow, ih]

theorem D_odd (n : Nat) : pairWith (D n) omegaOdd % 2 = 1 := by
  simp [D, rSegment_odd, omegaOdd, carry, r, rpow, s, rs]

theorem pairWith_mod2 (C : Chain n) (f g : Dic n → Dic n → Dic n → Int)
    (h : ∀ a b c, f a b c % 2 = g a b c % 2) :
    pairWith C f % 2 = pairWith C g % 2 := by
  induction C with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨⟨a,b,c⟩,k⟩
    simp only [pairWith_cons]
    rw [Int.add_emod, Int.add_emod (k*g a b c), ih]
    rw [Int.mul_emod, Int.mul_emod k (g a b c), h]

theorem D_even_nontrivial (n : Nat) :
    ¬ ∃ f : Dic n → Dic n → Int,
      ∀ a b c, omegaEven a b c % 2 = barDelta2 f a b c % 2 := by
  rintro ⟨f, h⟩
  have h := pairWith_mod2 (D n) omegaEven (barDelta2 f) h
  rw [D_even, D_pair_delta] at h
  contradiction

theorem D_odd_nontrivial (n : Nat) :
    ¬ ∃ f : Dic n → Dic n → Int,
      ∀ a b c, omegaOdd a b c % 2 = barDelta2 f a b c % 2 := by
  rintro ⟨f, h⟩
  have h := pairWith_mod2 (D n) omegaOdd (barDelta2 f) h
  rw [D_odd, D_pair_delta] at h
  contradiction

theorem D2_certificate :
    D 1 = [((r 1,r 1,r 1),1), ((r 1,s 1,s 1),-1), ((rs 1,rs 1,r 1),-1),
      ((rs 1,r 1,s 1),-1)] ∧ IsCycle (D 1) ∧ pairWith (D 1) omegaEven % 2 = 1 :=
  ⟨rfl, D_cycle 1, D_even 1⟩

end Q8Genus2Anomaly
