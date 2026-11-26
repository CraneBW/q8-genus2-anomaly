# Unpunctured Genus-2 Anomaly Detection for $Q_8$, $\mathrm{Dic}_N$, and All Finite Subgroups of $\mathrm{SU}(2)$

**An explicit closed, oriented, unpunctured genus-2 mapping torus carrying a flat $Q_8$-bundle pushes its fundamental class to $3 \bmod 8 \in H_3(BQ_8;\mathbb{Z}) \cong \mathbb{Z}/8\mathbb{Z}$ (phase $-1$ on the unique order-2 't Hooft anomaly $\alpha_4$), whereas the same order-2 anomaly evaluates to $+1$ on every closed genus-1 flat $Q_8$-bundle.**

This repository accompanies the manuscript [`paper/main.tex`](paper/main.tex) and provides two completely independent exact computational verification pipelines in Python (`src/path_a_bar.py`, `src/path_b_triangulation.py`), raw replayable certificates (`certificates/`), and a zero-`sorry`, zero-Mathlib **Lean 4.36.0** formalization (`lean/Q8Genus2Anomaly/`).

---

## Main Results

For a finite group $G$ and genus $g \ge 0$, define the **unpunctured genus-$g$ detection kernel**
$$K_g(G) \;\le\; H^3(BG; U(1))$$
as the joint kernel of single-bundle evaluation $\alpha \mapsto \langle \tilde{\rho}^*\alpha, [M_\phi]\rangle \in U(1)$ over all closed, oriented, unpunctured genus-$g$ mapping tori $M_\phi$ ($\phi \in \operatorname{Mod}(\Sigma_g)$) and all flat $G$-bundles $\tilde{\rho}: \pi_1(M_\phi) \to G$. Let $g_{\min}(G) := \min\{g \ge 0 : K_g(G) = 0\}$.

Let $\mathrm{Dic}_N = \langle r, s \mid r^{2N} = 1,\, s^2 = r^N,\, s r s^{-1} = r^{-1} \rangle$ ($N \ge 2$, order $4N$, with $Q_8 = \mathrm{Dic}_2$), so $H_3(B\mathrm{Dic}_N;\mathbb{Z}) \cong H^3(B\mathrm{Dic}_N;U(1)) \cong \mathbb{Z}/(4N)\mathbb{Z}$.

1. **Exact Genus-2 Single-Bundle Detection for Even $N \ge 2$**:
   On $\Sigma_2$ with $\pi_1(\Sigma_2) = \langle a,b,c,d \mid [a,b][c,d]=1\rangle$, $w = b a^{-1} b^{-1} c$, and standard disjoint Dehn twists $T_1 = T_a$, $T_3 = T_w$, $T_5 = T_c$, the mapping torus $M_\phi$ for
   $$\phi = T_1^N T_3^2 T_5^2, \qquad (\rho(a), \rho(b), \rho(c), \rho(d)) = (r, 1, s, 1), \qquad h = 1$$
   satisfies $\phi(R)=R$, $\rho\circ\phi=\rho$, $H_1(M_\phi;\mathbb{Z}) \cong \mathbb{Z}^3 \oplus \mathbb{Z}/2\mathbb{Z} \oplus \mathbb{Z}/(2N+2)\mathbb{Z}$, and in the orientation and Tomoda–Zvengrowski 4-periodic resolution generator $e_3$ pushes forward to
   $$\tilde{\rho}_*[M_\phi] \equiv N + 1 \pmod{4N} \quad \text{in } H_3(B\mathrm{Dic}_N;\mathbb{Z}) \cong \mathbb{Z}/(4N)\mathbb{Z}.$$
   Since $\gcd(N+1, 4N) = 1$ for every even $N \ge 2$, **this single unpunctured genus-2 flat bundle distinguishes all $4N$ anomaly classes** in $H^3(B\mathrm{Dic}_N;U(1))$, giving $K_2(\mathrm{Dic}_N) = 0$ and $g_{\min}(\mathrm{Dic}_N) = 2$ (and negative-phase witnesses for every $g \ge 2$).

2. **Complete ADE Classification for All Non-Trivial Finite Subgroups $G \le \mathrm{SU}(2)$**:
   For every non-trivial finite subgroup $G \le \mathrm{SU}(2)$ ($C_n$, $\mathrm{Dic}_N$, $2T$, $2O$, $2I$):
   - If the $2$-Sylow subgroup of $G$ is **cyclic** ($C_n$ and $\mathrm{Dic}_N$ with $N$ odd): $K_1(G) = 0$ and $g_{\min}(G) = 1$.
   - If the $2$-Sylow subgroup of $G$ is **generalized quaternion** ($\mathrm{Dic}_N$ with $N$ even, $2T$, $2O$, $2I$): $K_1(G) \cong \mathbb{Z}/2\mathbb{Z}$ (the unique order-$2$ subgroup), $K_2(G) = 0$, and $g_{\min}(G) = 2$.
   - In particular, **unpunctured genus-$2$ data detects $100\%$ of 't Hooft anomalies in $H^3(BG;U(1))$ for every finite subgroup $G \le \mathrm{SU}(2)$**.

3. **Precise Refinement of Yu (*Phys. Rev. D* 105, 106007, 2022)**:
   In M. Yu (`arXiv:2105.02231`, *Phys. Rev. D* **105**, 106007), Proposition 1.1 states a $\mathbb{Z}_2$ genus-1 detection kernel for $\mathrm{Dic}_N$ without restricting to even $N$, and Proposition 3.3 asserts that subgroups of $\mathrm{SU}(2)$ have no joint categorical Schur detector (Definition 3.2). For **odd $N \ge 3$**, $\langle s \rangle \cong C_4$ has odd index $N$ in $\mathrm{Dic}_N$, so the unique order-$2$ anomaly $\alpha_{2N}$ restricts to $2 \bmod 4$ on $C_4$ and evaluates to $-1$ on the genus-1 mapping torus $T_a^4$ with $(a,b;h) = (s,1;1)$ (giving $3 \bmod 12$ for $\mathrm{Dic}_3$); together with $\langle r \rangle \cong C_{2N}$, $\{C_4, C_{2N}\}$ is an abelian joint CSD and $K_1(\mathrm{Dic}_N) = 0$. Proposition 1.1 holds verbatim for **even $N \ge 2$**.

---

## Dual-Path Verification Summary

Paths **A** (`src/path_a_bar.py`) and **B** (`src/path_b_triangulation.py`) implement independent group arithmetic, fundamental-class constructions, and bundle colorings, sharing only the problem input specification and published Tomoda–Zvengrowski 4-periodic resolution differentials.

| $N$ | Witness | Free Filler Terms | Normalized Bar Terms (Path A) | Tetrahedra (Path B) | $H_1(M;\mathbb{Z})$ | Both Paths $\bmod 4N$ | $\bmod 2$ / Phase |
|---:|---|---:|---:|---:|---|---:|---:|
| 2 ($Q_8$) | Genus 2, $T_1^2 T_3^2 T_5^2$ | 114 | 18 | 6,744 | $\mathbb{Z}^3 \oplus \mathbb{Z}/2 \oplus \mathbb{Z}/6$ | **3 mod 8** | **1 / −1** |
| 3 ($\mathrm{Dic}_3$) | Genus 1, $T_a^4$ | 16 | 3 | 2,196 | $\mathbb{Z}^2 \oplus \mathbb{Z}/4$ | **3 mod 12** | **1 / −1** |
| 4 ($\mathrm{Dic}_4$) | Genus 2, $T_1^4 T_3^2 T_5^2$ | 120 | 20 | 8,280 | $\mathbb{Z}^3 \oplus \mathbb{Z}/2 \oplus \mathbb{Z}/10$ | **5 mod 16** | **1 / −1** |
| 6 ($\mathrm{Dic}_6$) | Genus 2, $T_1^6 T_3^2 T_5^2$ | 126 | 22 | 9,816 | $\mathbb{Z}^3 \oplus \mathbb{Z}/2 \oplus \mathbb{Z}/14$ | **7 mod 24** | **1 / −1** |

Additional independent checks verified in `tests/test_verification.py` (10/10 passing):
- **Non-real orientation calibration**: $L(4,1)$ algebraic bar cycle (3 terms) and geometric quotient (96 tetrahedra) both evaluate to $1 \bmod 4$ ($+i$); reversed orientation gives $3 \bmod 4$ ($-i$), certifying orientation multiplier $+1$.
- **Spherical space form $S^3/Q_8$**: 48-tetrahedron quotient $(V,E,F,T)=(10,58,96,48)$ passes face-orientation, $S^1$ edge-link, $S^2$ vertex-link, and flatness checks, evaluating to $1 \bmod 8$ (phase $-1$).
- **Independent $\bmod 8$ cocycle tables**: Path A (Tomoda–Zvengrowski contracting homotopy) and Path B (Smith normal form over Hamilton quaternions) yield distinct normalized $\mathbb{Z}/8$ 3-cocycles $W_A \neq W_B$; `tests/test_verification.py` solves for an explicit 2-cochain $u$ satisfying $W_B - W_A \equiv \delta u \pmod 8$ on all $512$ triples.
- **Exhaustive $Q_8$ genus-1 regression**:
  - Path A: all $48 \times 40 \times 8 = 15,360$ candidates in $\mathrm{SL}_2(\mathbb{Z}/4) \times \{\text{commuting pairs}\} \times Q_8$ yield **1,920** valid flat bundles; all 1,920 bar 3-cycles verify $\partial = 0$ and phase **$+1$**.
  - Path B: action graph on 40 commuting pairs has 5 orbits (sizes $1, 3, 12, 12, 12$), 35 spanning-tree edges, and **125** non-tree stabilizer generator loops; all 125 loops are explicitly triangulated (**596,304** tetrahedra total), yielding phase **$+1$** on every loop.

---

## Pure Lean 4.36.0 Formalization Scope

The standalone package `lean/Q8Genus2Anomaly/` (no Mathlib dependency) declares **89 theorems** across six modules (`Group.lean`, `Cocycle.lean`, `Bar.lean`, `FreeWords.lean`, `Torus.lean`, `Odd.lean`), with **43 named main theorems** audited via `#print axioms` in `Audit.lean`:
- **Zero `sorry`**, **zero `admit`**, **zero custom axioms**, **zero `Classical.choice`** (5 theorems have no axiom dependencies; 38 depend only on `[propext, Quot.sound]`).
- **Proved inside the Lean kernel**:
  - Group axioms for general $\mathrm{Dic}_N$ ($N = n+1$) and $Q_8$, plus homomorphisms $x, y, q$.
  - Normalized 3-cocycle identities $\delta\omega_{\text{even}} \equiv 0 \pmod 2$ (for all even $N$, plus 4,096-tuple exhaustion for $Q_8$) and $\delta\omega_{\text{odd}} \equiv 0 \pmod 2$ (for all odd $N$).
  - Integral 3-cycle $D_N$: $\partial D_N = 0$, $\omega_{\text{even}}(D_N) \equiv 1 \pmod 2$, $\omega_{\text{odd}}(D_N) \equiv 1 \pmod 2$, and non-coboundary theorems `D_even_nontrivial`, `D_odd_nontrivial` for all $N$.
  - Five genus-2 Dehn twists preserve $R = [a,b][c,d]$; $\phi = T_1^2 T_3^2 T_5^2$ fixes $R$ and $\rho$; Cayley-tree free filler satisfies $\partial L = \phi(C) - C$; its pushforward `ZA` (18 terms) satisfies $\partial Z_A = 0$ and $\omega_{\text{even}}(Z_A) \equiv 1 \pmod 2$.
  - Exhaustive $Q_8$ finite torus half-difference theorem (`q8_torus_blind`, 1,920 valid configurations across $\mathrm{SL}_2(\mathbb{Z}/4)$) and lift-invariance (`halfDifference_lift`).
  - General odd-$N$ genus-1 counterexample (`odd_torus_counterexample`, all odd $N$) plus explicit `pushChain` check for $\mathrm{Dic}_3$ (`dic3_ta4_bar_lift`).
- **Topological bridges proved analytically in `paper/main.tex` (outside the Lean kernel)**:
  - Identification of $\rho_*L + P_h(C)$ with the oriented fundamental class $\tilde{\rho}_*[M_\phi]$ via the punctured-fiber relative fundamental class;
  - Reduction of $\mathrm{SL}(2,\mathbb{Z})$ to $\mathrm{SL}_2(\mathbb{Z}/4)$ and equality of the Bockstein/Wang half-difference pairing with $\langle \tilde{\rho}^*\omega_2, [M_\phi]\rangle$;
  - General even-$N$ group-ring proof of $(N+1)\bmod 4N$, Path B simplicial triangulations, and the full ADE classification for $G \le \mathrm{SU}(2)$.

---

## Reproducing Everything

### Python Dual-Path Suite
```bash
python3 -m venv .venv
.venv/bin/pip install sympy numpy scipy pytest
.venv/bin/python src/path_a_bar.py
.venv/bin/python src/path_b_triangulation.py
.venv/bin/python -m pytest -v
```
*(Interface note: `src/path_a_bar.py`'s mod-4 torus regression and `src/path_b_triangulation.py`'s single-character orbit edge-color encoding are specialized to $Q_8$ of order $8$; `lean/Q8Genus2Anomaly/FreeWords.lean` assumes generator letters lie in the declared alphabet.)*

### Lean 4.36.0 Verification
```bash
cd lean
lake build
```
Raw verification logs are archived in [`certificates/pytest.log`](certificates/pytest.log) and [`certificates/lean_build.log`](certificates/lean_build.log); see also [`docs/PHASE1_AUDIT.md`](docs/PHASE1_AUDIT.md).

---

## Repository Structure

```text
├── README.md
├── LICENSE
├── paper/
│   └── main.tex                        # Self-contained arXiv-ready manuscript
├── src/
│   ├── path_a_bar.py                   # Algebraic bar 3-cycles & Tomoda-Zvengrowski mod-4N cocycles
│   └── path_b_triangulation.py         # Independent 3-manifold triangulations & single-bundle DW
├── tests/
│   └── test_verification.py            # 10 cross-path replay, coboundary, and regression tests
├── certificates/
│   ├── path_a_certificates.json        # Raw algebraic certificates
│   ├── path_b_certificates.json        # Raw triangulation & 125-loop stabilizer certificates
│   ├── pytest.log                      # Full pytest verification log
│   └── lean_build.log                  # Full Lean 4.36.0 build + 43 #print axioms log
├── lean/
│   ├── lean-toolchain                  # leanprover/lean4:v4.36.0
│   ├── lakefile.toml
│   └── Q8Genus2Anomaly/
│       ├── Group.lean                  # General Dic_N and Q_8 group axioms & homomorphisms
│       ├── Cocycle.lean                # Normalized mod-2 3-cocycles (even & odd N)
│       ├── Bar.lean                    # Integral bar chains, D_N, non-coboundary proofs
│       ├── FreeWords.lean              # 5 Dehn twists, Cayley-tree filler, 18-term Q_8 witness Z_A
│       ├── Torus.lean                  # Exhaustive 48×40×8 Q_8 half-difference vanishing & lift
│       ├── Odd.lean                    # General odd-N genus-1 counterexample & Dic_3 bar lift
│       └── Audit.lean                  # #print axioms audit of 43 core theorems
└── docs/
    ├── PROBLEM_BRIEF.md
    ├── THEORY_BLUEPRINT.md
    └── PHASE1_AUDIT.md
```
