import Std

namespace Q8Genus2Anomaly

/-- The index n represents N = n+1. A rotation and a j-bit give 4N elements. -/
abbrev Dic (n : Nat) := Fin (2*n+2) × Bool
abbrev Q8 := Dic 1

def half (n : Nat) : Int := (n : Int) + 1
def period (n : Nat) : Int := 2*n + 2

theorem period_pos (n : Nat) : 0 < period n := by simp [period]; omega

def ofInt (n : Nat) (p : Int) (b : Bool) : Dic n :=
  (⟨(p % period n).toNat, by
    have h := Int.emod_lt_of_pos p (period_pos n)
    change (p % period n).toNat < 2*n+2
    unfold period at *
    omega⟩, b)

def rotation (g : Dic n) : Int := g.1.val

@[simp] theorem rotation_ofInt (p : Int) (b : Bool) :
    rotation (ofInt n p b) = p % period n := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg p (by have := period_pos n; omega))

theorem rotation_nonneg (g : Dic n) : 0 ≤ rotation g := Int.natCast_nonneg _
theorem rotation_lt (g : Dic n) : rotation g < period n := by
  have h := g.1.isLt
  simp [period, rotation]
  omega

theorem ofInt_congr {p q : Int} {b : Bool} (h : p % period n = q % period n) :
    ofInt n p b = ofInt n q b := by
  simp [ofInt, h]

@[simp] theorem ofInt_rotation (g : Dic n) : ofInt n (rotation g) g.2 = g := by
  apply Prod.ext
  · apply Fin.ext
    change (rotation g % period n).toNat = g.1.val
    rw [Int.emod_eq_of_lt (rotation_nonneg g) (rotation_lt g)]
    rfl
  · rfl

def one (n : Nat) : Dic n := ofInt n 0 false
def rpow (n : Nat) (i : Int) : Dic n := ofInt n i false
def r (n : Nat) : Dic n := rpow n 1
def s (n : Nat) : Dic n := ofInt n 0 true
def rs (n : Nat) : Dic n := ofInt n 1 true
def z (n : Nat) : Dic n := rpow n (half n)

def raw (n : Nat) (p q : Int) : Bool → Bool → Int
  | false, _ => p+q
  | true, false => p-q
  | true, true => p-q+half n

def mul (g h : Dic n) : Dic n :=
  ofInt n (raw n (rotation g) (rotation h) g.2 h.2) (g.2 ^^ h.2)

def inv (g : Dic n) : Dic n :=
  if g.2 then ofInt n (rotation g - half n) true else ofInt n (-rotation g) false

theorem raw_mod (p q : Int) (a b : Bool) :
    raw n (p % period n) (q % period n) a b % period n =
      raw n p q a b % period n := by
  cases a <;> cases b <;> simp [raw]
  rw [← Int.emod_add_emod (p % period n - q % period n) (period n)]
  rw [Int.emod_sub_emod, Int.sub_emod_emod, Int.emod_add_emod]

@[simp] theorem mul_ofInt (p q : Int) (a b : Bool) :
    mul (ofInt n p a) (ofInt n q b) = ofInt n (raw n p q a b) (a ^^ b) := by
  apply ofInt_congr
  simp only [rotation_ofInt]
  exact raw_mod p q a b

theorem congr_small {p q : Int}
    (h : p = q ∨ p = q + period n ∨ p = q - period n) :
    p % period n = q % period n := by
  rcases h with h | h | h <;> simp [h]

theorem dic_assoc (g h k : Dic n) : mul (mul g h) k = mul g (mul h k) := by
  rw [← ofInt_rotation g, ← ofInt_rotation h, ← ofInt_rotation k]
  simp only [mul_ofInt]
  cases g.2 <;> cases h.2 <;> cases k.2 <;> apply ofInt_congr <;>
    apply congr_small <;> simp [raw, period, half] <;>
    omega

theorem dic_one_mul (g : Dic n) : mul (one n) g = g := by
  have h : mul (one n) (ofInt n (rotation g) g.2) = ofInt n (rotation g) g.2 := by
    rw [one, mul_ofInt]
    cases g.2 <;> simp [raw]
  simpa only [ofInt_rotation] using h

theorem dic_mul_one (g : Dic n) : mul g (one n) = g := by
  rw [← ofInt_rotation g]
  cases g.2 <;> simp [one, raw]

theorem dic_inv_ofInt (p : Int) (b : Bool) :
    inv (ofInt n p b) = ofInt n (if b then p - half n else -p) b := by
  cases b
  · apply ofInt_congr
    change (-rotation (ofInt n p false)) % period n = (-p) % period n
    rw [rotation_ofInt, Int.neg_emod_eq_sub_emod, Int.sub_emod_emod,
      ← Int.neg_emod_eq_sub_emod]
  · apply ofInt_congr
    change (rotation (ofInt n p true) - half n) % period n = (p-half n) % period n
    simp

theorem dic_mul_inv (g : Dic n) : mul g (inv g) = one n := by
  rw [← ofInt_rotation g, dic_inv_ofInt, mul_ofInt]
  cases g.2 <;> apply ofInt_congr <;> apply congr_small <;>
    simp [raw, half, period] <;> omega

theorem dic_inv_mul (g : Dic n) : mul (inv g) g = one n := by
  rw [← ofInt_rotation g, dic_inv_ofInt, mul_ofInt]
  cases g.2 <;> apply ofInt_congr <;>
    congr 1 <;> simp [raw, half] <;> omega

theorem q8_group :
    (∀ g h k : Q8, mul (mul g h) k = mul g (mul h k)) ∧
    (∀ g : Q8, mul (one 1) g = g ∧ mul g (one 1) = g ∧
      mul g (inv g) = one 1 ∧ mul (inv g) g = one 1) :=
  ⟨dic_assoc, fun g => ⟨dic_one_mul g, dic_mul_one g, dic_mul_inv g, dic_inv_mul g⟩⟩

@[simp] theorem rpow_zero : rpow n 0 = one n := rfl

theorem r_rpow (i : Int) : mul (r n) (rpow n i) = rpow n (i+1) := by
  simp [r, rpow, raw, Int.add_comm]

theorem rpow_r (i : Int) : mul (rpow n i) (r n) = rpow n (i+1) := by
  simp [r, rpow, raw]

theorem r_s : mul (r n) (s n) = rs n := by simp [r, rpow, s, rs, raw]
theorem s_s : mul (s n) (s n) = z n := by simp [s, z, rpow, raw]
theorem rs_rs : mul (rs n) (rs n) = z n := by simp [rs, z, rpow, raw]
theorem rs_r : mul (rs n) (r n) = s n := by simp [rs, r, rpow, s, raw]

def x (g : Dic n) : Int := rotation g % 2
def y (g : Dic n) : Int := if g.2 then 1 else 0
def q (g : Dic n) : Int := (2*rotation g + y g) % 4

theorem two_dvd_period (n : Nat) : (2 : Int) ∣ period n := ⟨half n, by simp [period, half]; omega⟩

@[simp] theorem x_ofInt (p : Int) (b : Bool) : x (ofInt n p b) = p % 2 := by
  simp [x, Int.emod_emod_of_dvd _ (two_dvd_period n)]

@[simp] theorem y_ofInt (p : Int) (b : Bool) : y (ofInt n p b) = if b then 1 else 0 := rfl

theorem x_mul (even : half n % 2 = 0) (g h : Dic n) :
    x (mul g h) = (x g + x h) % 2 := by
  rw [← ofInt_rotation g, ← ofInt_rotation h, mul_ofInt]
  cases g.2 <;> cases h.2 <;> simp [x_ofInt, raw] <;> omega

theorem y_mul (g h : Dic n) : y (mul g h) = (y g + y h) % 2 := by
  rw [← ofInt_rotation g, ← ofInt_rotation h, mul_ofInt]
  cases g.2 <;> cases h.2 <;> rfl

@[simp] theorem q_ofInt (p : Int) (b : Bool) :
    q (ofInt n p b) = (2*p + (if b then 1 else 0)) % 4 := by
  have h : (p % period n) % 2 = p % 2 := Int.emod_emod_of_dvd p (two_dvd_period n)
  simp only [q, rotation_ofInt, y_ofInt]
  omega

theorem q_mul (odd : half n % 2 = 1) (g h : Dic n) :
    q (mul g h) = (q g + q h) % 4 := by
  rw [← ofInt_rotation g, ← ofInt_rotation h, mul_ofInt]
  cases g.2 <;> cases h.2 <;> simp [q_ofInt, raw] <;> omega

end Q8Genus2Anomaly
