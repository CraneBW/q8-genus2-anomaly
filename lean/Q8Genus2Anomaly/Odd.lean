import Q8Genus2Anomaly.FreeWords
import Q8Genus2Anomaly.Torus

namespace Q8Genus2Anomaly

theorem powG_add (g : Dic n) (a b : Nat) : powG g (a+b) = mul (powG g a) (powG g b) := by
  induction b with
  | zero => exact (dic_mul_one _).symm
  | succ b ih =>
    change mul (powG g (a+b)) g = mul (powG g a) (mul (powG g b) g)
    rw [ih, dic_assoc]

theorem powG_one (g : Dic n) : powG g 1 = g := dic_one_mul g

def sThird (n : Nat) : Dic n := ofInt n (half n) true

theorem z_s (n : Nat) : mul (z n) (s n) = sThird n := by
  simp [z, rpow, s, sThird, raw]

theorem sThird_s (n : Nat) : mul (sThird n) (s n) = one n := by
  simp only [sThird, s, mul_ofInt, raw, Int.sub_zero, one]
  apply ofInt_congr
  rw [show half n + half n = period n by simp [half, period]; omega]
  simp

theorem s_order_four (n : Nat) : powG (s n) 4 = one n := by
  simp only [powG, dic_one_mul, s_s, z_s, sThird_s]

theorem sPow_multiple_four (n k : Nat) : powG (s n) (4*k) = one n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, powG_add, ih, s_order_four, dic_one_mul]

theorem sPow_reduce (n k : Nat) : powG (s n) (k%4) = powG (s n) k := by
  have h := congrArg (powG (s n)) (Nat.mod_add_div k 4)
  rwa [powG_add, sPow_multiple_four, dic_mul_one] at h

theorem c4_embedding_mul (n a b : Nat) :
    mul (powG (s n) (a%4)) (powG (s n) (b%4)) = powG (s n) ((a+b)%4) := by
  rw [← powG_add, ← sPow_reduce n (a%4+b%4),
    show (a%4+b%4)%4 = (a+b)%4 by omega]

theorem q_sPow (odd : half n % 2 = 1) (k : Nat) :
    q (powG (s n) k) = (k : Int)%4 := by
  induction k with
  | zero => simp [powG, one]
  | succ k ih =>
    have h : q (s n) = 1 := by simp [s]
    rw [powG, q_mul odd, ih, h, Int.natCast_succ]
    simp

theorem c4_embedding_injective (odd : half n % 2 = 1) (a b : Fin 4)
    (h : powG (s n) a.val = powG (s n) b.val) : a = b := by
  have hq := congrArg q h
  rw [q_sPow odd, q_sPow odd] at hq
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

def cyclicExponent (w : Word) : Nat :=
  w.foldl (fun e l => (e + (if l=1 then 1 else if l = -1 then 3 else 0))%4) 0

def ta4FreeChain : WChain3 := treeFiller (movedDifference torusRelator ta4)

def ta4CyclicChain : List ((Nat × Nat × Nat) × Int) :=
  collect (ta4FreeChain.filterMap fun ((a,b,c),k) =>
    let (r,s,t) := (cyclicExponent a,cyclicExponent b,cyclicExponent c)
    if r = 0 ∨ s = 0 ∨ t = 0 then none else some ((r,s,t),k))

theorem ta4_cyclic_certificate :
    ta4CyclicChain = [((1,1,1),1), ((1,2,1),1), ((1,3,1),1)] := by decide

def oddTorusChain (n : Nat) : Chain n :=
  ta4CyclicChain.map (fun ((a,b,c),k) => ((powG (s n) a,powG (s n) b,powG (s n) c),k))

def torusRho (n : Nat) : Array (Dic n) := #[s n,one n]

theorem ta4_preserves_rho (n : Nat) :
    ta4.toList.map (wordHolonomy (torusRho n)) = (torusRho n).toList ∧
      wordHolonomy (torusRho n) torusRelator = one n := by
  change [mul (one n) (s n),mul (mul (mul (mul (mul (one n) (one n)) (s n)) (s n)) (s n)) (s n)] =
      [s n,one n] ∧ mul (mul (mul (mul (one n) (s n)) (one n)) (inv (s n))) (inv (one n)) = one n
  simp only [dic_mul_one, dic_one_mul, dic_mul_inv]
  exact ⟨congrArg (fun u => [s n,u]) (by
    simpa only [powG, dic_one_mul] using s_order_four n), True.intro⟩

theorem odd_torus_cycle (n : Nat) : IsCycle (oddTorusChain n) := by
  intro a b
  unfold barBoundary oddTorusChain
  rw [ta4_cyclic_certificate]
  have left : ∀ k : Nat, mul (powG (s n) 1) (powG (s n) k) = powG (s n) (k+1) := by
    intro k
    rw [← powG_add, Nat.add_comm]
  have right : ∀ k : Nat, mul (powG (s n) k) (powG (s n) 1) = powG (s n) (k+1) := by
    intro k
    rw [← powG_add]
  simp only [List.map_cons, List.map_nil, pairWith_cons, pairWith_nil,
    Int.one_mul, barDelta2, left, right, Nat.reduceAdd, s_order_four]
  have h₁ : indicator2 a b (powG (s n) 1) (one n) = 0 := by simp [indicator2]
  have h₂ : indicator2 a b (one n) (powG (s n) 1) = 0 := by simp [indicator2]
  omega

theorem odd_torus_phase (odd : half n % 2 = 1) : pairWith (oddTorusChain n) omegaOdd % 2 = 1 := by
  simp [oddTorusChain, ta4_cyclic_certificate, omegaOdd, carry, q_sPow odd]

theorem odd_torus_counterexample (odd : half n % 2 = 1) :
    Normalized (n := n) omegaOdd ∧
    (∀ a b c d : Dic n, delta omegaOdd a b c d % 2 = 0) ∧
    substitute ta4 torusRelator = torusRelator ∧
    ta4.toList.map (wordHolonomy (torusRho n)) = (torusRho n).toList ∧
    wordHolonomy (torusRho n) torusRelator = one n ∧
    IsCycle (oddTorusChain n) ∧ pairWith (oddTorusChain n) omegaOdd % 2 = 1 :=
  ⟨odd_normalized n, odd_cocycle odd, ta4_preserves_R, (ta4_preserves_rho n).1,
    (ta4_preserves_rho n).2, odd_torus_cycle n, odd_torus_phase odd⟩

theorem dic3_torus_counterexample :
    IsCycle (oddTorusChain 2) ∧ pairWith (oddTorusChain 2) omegaOdd % 2 = 1 :=
  ⟨odd_torus_cycle 2, odd_torus_phase (by decide)⟩

theorem dic3_ta4_bar_lift :
    pushChain ta4FreeChain (torusRho 2) = oddTorusChain 2 := by decide

end Q8Genus2Anomaly
