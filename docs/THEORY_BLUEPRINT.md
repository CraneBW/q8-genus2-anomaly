# Phase 1 Theoretical Blueprint & Verification Specification (by Astra Max)

**Date**: 2026-11-26
**Status**: Analytical proof complete & hand-checked by Antigravity; awaiting dual-path Python certificates and Lean 4 formalization.

---

## 1. Main Theorem (Classification for $\mathrm{Dic}_N$, $N \ge 2$)

Let $\mathrm{Dic}_N = \langle r, s \mid r^{2N} = 1,\, s^2 = r^N,\, s r s^{-1} = r^{-1} \rangle$ (order $4N$, central element $z = r^N = s^2$, $Q_8 = \mathrm{Dic}_2$). Elements are written $(p, q) = r^p s^q$ with $0 \le p < 2N$, $q \in \{0,1\}$, and multiplication
$$(p, q)(u, v) = \big(p + (-1)^q u + N q v \bmod 2N,\; q \oplus v\big).$$
For $Q_8$ ($r=i, s=j$), indexing $(1, i, -1, -i, j, k, -j, -k)$ as $0..7$, the $8\times 8$ multiplication table (row = left factor, col = right factor) is:
`01234567 / 12305674 / 23016745 / 30127456 / 47652103 / 54763210 / 65470321 / 76541032`.

Let $\alpha_{2N} \in H^3(B\mathrm{Dic}_N; U(1)) \cong \mathbb{Z}/(4N)\mathbb{Z}$ be the unique order-2 anomaly class. Then the minimum genus $g_{\min}(\mathrm{Dic}_N)$ of a closed, oriented, **unpunctured** surface $\Sigma_g$ whose mapping-torus stack $\mathcal{M}_g^{\mathrm{Dic}_N}$ detects $\alpha_{2N}$ (and indeed the entire group $H^3(B\mathrm{Dic}_N; U(1))$) is:
- **$g_{\min}(\mathrm{Dic}_N) = 2$ for every even $N \ge 2$** (in particular **$g_{\min}(Q_8) = 2$**), with negative-phase witnesses at every $g \ge 2$;
- **$g_{\min}(\mathrm{Dic}_N) = 1$ for every odd $N \ge 3$** (with $K_1(\mathrm{Dic}_N) = 0$, giving an explicit counterexample to a literal all-$N$ reading of Yu's Proposition 1.1 and Proposition 3.3 in `arXiv:2105.02231` / *Phys. Rev. D* **105**, 106007).

---

## 2. Explicit Normalized 3-Cocycles & 4-Term Bar 3-Cycle Certificate

### Even $N \ge 2$
- Group homomorphisms to $\mathbb{Z}/2$: $x(p,q) = p \bmod 2$, $y(p,q) = q$.
- Normalized $\mathbb{Z}/2$-valued 3-cocycle:
  $$\omega_2(g, h, k) = x(g) x(h) y(k) \pmod 2.$$
- Integral normalized bar 3-cycle:
  $$D_N = \sum_{j=1}^{N-1} [r | r^j | r] - [r | s | s] - [rs | rs | r] - [rs | r | s].$$
  - $\partial D_N = 0$ identically over $\mathbb{Z}$;
  - $\omega_2(D_N) = -1 \equiv 1 \pmod 2$ (only the last term contributes);
  - $[D_N]$ generates $H_3(\mathrm{Dic}_N; \mathbb{Z}) \cong \mathbb{Z}/(4N)\mathbb{Z}$ (image of the 3-cell of the Tomoda–Zvengrowski 4-periodic resolution, `arXiv:0904.1876`, Prop. 3.2–3.3).
  - For $Q_8$: $D_2 = [i|i|i] - [i|j|j] - [k|k|i] - [k|i|j]$.
- Full $\mathbb{Z}/8$-valued 3-cocycle $W_8$ for $Q_8$: built via the Tomoda–Zvengrowski 4-periodic resolution $P$ and contracting homotopy $s$ (`arXiv:0904.1876` Prop. 3.2–3.3): define $F_0([]) = e_0$, $F_n(B) = s_{n-1} F_{n-1}(\partial_{\mathrm{free}} B)$ on free bar basis (keeping left coefficient $g_1$ in the first boundary term!), extend $\mathbb{Z}G$-linearly, and set $W_8(B) = \varepsilon(F_3(B)/e_3) \bmod 8$. Must satisfy $\delta W_8 = 0$, $W_8(D_2) \equiv \pm 1 \pmod 8$, and $W_8 \bmod 2 - \omega_2 = \delta v$ for an explicit 2-cochain $v$.

### Odd $N \ge 3$
- Group homomorphism $q: \mathrm{Dic}_N \to \mathbb{Z}/4$ given by $q(r) = 2$, $q(s) = 1$ (well-defined since $2\cdot 2N \equiv 0$, $2\cdot 1 = 2 \equiv 2N \pmod 4$, and $-2 \equiv 2 \pmod 4$).
- Normalized $\mathbb{Z}/2$-valued 3-cocycle for $\alpha_{2N}$:
  $$\omega_2^{\mathrm{odd}}(g, h, k) = (q(g) \bmod 2) \left\lfloor \frac{\hat{q}(h) + \hat{q}(k)}{4} \right\rfloor \pmod 2, \quad \hat{q} \in \{0,1,2,3\}.$$
- Genus-1 witness: $\gamma = T_a^4 : (a,b) \mapsto (a, b a^4)$ on $T^2$ with $\rho(a) = s, \rho(b) = 1, h = 1$ gives phase $-1$ (and for $N=3$, $C_4$ + $C_6$ give $\ker(\int_{T^2}) = 0$).

---

## 3. Explicit Genus-2 Generators & Witness ($\phi = T_1^N T_3^2 T_5^2$)

Set $(a, b, c, d) = (a_1, b_1, a_2, b_2)$, $R = [a,b][c,d]$, $w = b a^{-1} b^{-1} c$ (so $R = a w d c^{-1} d^{-1}$).
Free-group lifts (composition right-to-left, unlisted generators fixed):
- $T_1 = T_a$: $b \mapsto b a$
- $T_2 = T_b$: $a \mapsto a b^{-1}$
- $T_3 = T_w$: $b \mapsto w^{-1} b$, $c \mapsto w^{-1} c w$, $d \mapsto d w$
- $T_4 = T_d$: $c \mapsto c d^{-1}$
- $T_5 = T_c$: $d \mapsto d c$
- Hyperelliptic involution lift: $T_5 T_4 T_3 T_2 T_1^2 T_2 T_3 T_4 T_5$.

**Explicit Witness (every even $N \ge 2$)**:
$$\phi = T_1^N T_3^2 T_5^2, \qquad (\rho(a), \rho(b), \rho(c), \rho(d)) = (r, 1, s, 1), \qquad h = 1.$$
- Strictly satisfies $\phi(R) = R$ in $F_4$ and $\rho \circ \phi = \rho$ in $\mathrm{Dic}_N$.
- Induced homology action: $a \mapsto a$, $c \mapsto c$, $b \mapsto b + (N+2)a - 2c$, $d \mapsto d - 2a + 4c$.
- For $Q_8$ ($N=2$): $H_1(M_\phi; \mathbb{Z}) \cong \mathbb{Z}^3 \oplus \mathbb{Z}/2\mathbb{Z} \oplus \mathbb{Z}/6\mathbb{Z}$.
- Bockstein / Wang pairing:
  $$\langle u^2 v, [M_\phi] \rangle = \left\langle \left(\frac{\phi^* X - X}{2} \bmod 2\right) \smile v|_{\Sigma_2}, [\Sigma_2] \right\rangle = \left\langle \left(\frac{N+2}{2} b^* - d^*\right) \smile c^*, [\Sigma_2] \right\rangle \equiv 1 \pmod 2.$$

---

## 4. Dual-Path Implementation & Verification Requirements

Paths **A** and **B** must be implemented **completely independently** (separate group arithmetic, fundamental chain/triangulation builder, and bundle coloring; sharing only the problem input specification and output comparison).

### Path A: Algebraic Bar 3-Cycle & 4-Periodic Resolution (`src/path_a_bar.py`)
1. Exact free-group word arithmetic (`±1..±4`), verify all 5 Dehn twists preserve $R = [a,b][c,d]$ identically.
2. Verify $\delta\omega_2 = 0$ on all $8^4 = 4096$ quadruples, $\partial D_2 = 0$, $\omega_2(D_2) \equiv 1 \pmod 2$.
3. Construct full mod-8 cocycle $W_8$ via Tomoda–Zvengrowski 4-periodic resolution + contracting homotopy $s$; verify $\delta W_8 = 0$ on all 4096 quadruples, $W_8(D_2) \equiv \pm 1 \pmod 8$, and find explicit 2-cochain $v$ with $W_8 \bmod 2 - \omega_2 = \delta v$.
4. Construct surface bar 2-chain $C = \sum_j [p_{j-1} | \ell_j] - \sum_{\ell_j = e^{-1}} [e^{-1} | e]$ ($\partial C = -[R]$ in $F_4$) and Cayley-tree contracting homotopy $K_2$ giving $L = K_2(\phi C - C)$ ($\partial L = \phi C - C$ in $F_4$). Push forward to $Z_A = \rho_* L$ (plus conjugation prism $P_h(C)$ for general $h$).
5. Verify $\partial Z_A = 0$ over $\mathbb{Z}$, evaluate both $\omega_2(Z_A) \equiv 1 \pmod 2$ and $W_8(Z_A) \pmod 8$ (must be odd!).
6. Run full genus-1 exhaustive regression for $Q_8$: all 48 matrices in $\mathrm{SL}_2(\mathbb{Z}/4)$ × all 40 ordered commuting pairs × all 8 $h \in Q_8$ satisfying $\gamma \triangleright (x,y) = (x,y) \triangleleft h$ — verify **100% give phase $+1$** (and also verify non-real orientation calibration on a cyclic $C_4$ Lens space $L(4,1)$!).
7. Run witnesses for $N=2$ ($Q_8$), $N=3$ (odd counterexample at genus 1: $T_a^4$ gives $-1$), $N=4$ ($\mathrm{Dic}_4$, $v_2(N)=2$, genus 2 gives $-1$), and $N=6$ ($\mathrm{Dic}_6$, $v_2(N)=1$, genus 2 gives $-1$).

### Path B: Geometric Closed Oriented 3-Manifold Triangulation & Single-Bundle DW (`src/path_b_triangulation.py`)
1. Construct the closed oriented genus-2 mapping torus $M_\phi$ directly geometrically from two pairs of pants (each built from two hexagons glued along 3 alternating edges) closed along three annular seams $a, w, c$ with piecewise-linear Dehn shear $(θ, u) \mapsto (θ + m u, u)$ for $(m_a, m_w, m_c) = (N, 2, 2)$ and common subdivision of $K$ and $\phi K$ at the mid-slice, coning each 3-cell boundary to an interior vertex, gluing ends via $(p,0) \sim (\phi(p), 1)$ so $t \gamma t^{-1} = \phi(\gamma)$.
2. Implement independent Hamilton unit-quaternion group arithmetic; color the 1-skeleton by fixing holonomies along the 5 marked loops $a, b, c, d, t$ in maximal-tree gauge.
3. Explicitly certify topology & flatness from raw triangulation data:
   - Every 2-face appears in exactly two 3-simplices with **opposite induced orientations** ($\partial [M_\phi] = 0$ identically over $\mathbb{Z}$);
   - Every edge link is a single simple cycle ($S^1$);
   - Every vertex link is a connected closed orientable surface with Euler characteristic $\chi = 2$ ($S^2$);
   - Cutting certificate along the fiber recovers $\Sigma_2 \times [0,1]$;
   - Every 2-simplex satisfies flatness $g_{01} g_{12} = g_{02}$;
   - Compute $H_1(M_\phi; \mathbb{Z})$ via Smith Normal Form and verify $\mathbb{Z}^3 \oplus \mathbb{Z}/2\mathbb{Z} \oplus \mathbb{Z}/6\mathbb{Z}$ for $Q_8$!
4. Evaluate single-bundle DW weight $\prod_\Delta (-1)^{\varepsilon_\Delta x(g_{01}) x(g_{12}) y(g_{23})}$ and full $W_8$ mod-8 sum; verify **phase $= -1$** (and match Path A's mod-8 value after orientation calibration via a non-real cyclic $C_4$ Lens space!).
5. Spherical space form $S^3 / Q_8$ calibration: barycentric subdivision of $\partial\operatorname{conv}(\pm 1, \pm i, \pm j, \pm k)$ modulo left $Q_8$-action (48 tetrahedra), verify manifold conditions, flatness, and phase $= -1$ (and mod-8 value $\pm 1 \bmod 8$).
6. Genus-1 geometric regression: build the action graph on all 40 commuting pairs under $S, T$ and gauge conjugations $i, j$; take a spanning tree per orbit and triangulate every non-tree stabilizer generator loop; verify ALL yield $+1$ for $Q_8$, and triangulate the $N=3$ $T_a^4$ witness yielding $-1$.

### Lean 4 Formalization (`lean/Q8Genus2Anomaly/`)
Pure Lean 4.36.0 (no external Mathlib dependency, zero `sorry`, zero custom axioms, passes `lake build`):
1. Exact definition of $Q_8$ and general $\mathrm{Dic}_N$, group laws proved.
2. Exact $\omega_2$ cocycle for even $N$ (and $\omega_2^{\mathrm{odd}}$ for odd $N$), machine-checked $\delta\omega_2 = 0$ (all 4096 quadruples for $Q_8$ and general algebraic proof for all even $N$!).
3. Exact 4-term bar cycle $D_2$ (and $D_N$): proved $\partial D_2 = 0$ and $\omega_2(D_2) = 1$ (certifying nontriviality & exact order-2 class).
4. Exact $Q_8$ genus-2 bar 3-cycle certificate $Z_A$ (and/or simplicial triangulation certificate from Path B!): machine-checked $\partial Z_A = 0$ identically over $\mathbb{Z}$ and $\omega_2(Z_A) \equiv 1 \pmod 2$, plus verified homomorphism $\rho \circ \phi = \rho$ and $\phi(R) = R$ in $F_4$!
5. Exact $Q_8$ genus-1 finite half-difference theorem: machine-checked exhaustive proof over all 48 matrices in $\mathrm{SL}_2(\mathbb{Z}/4)$, all 40 commuting pairs, and all $h \in Q_8$ (1,920 valid configurations) that the Bockstein/Wang half-difference pairing vanishes mod 2 (and is invariant under lifting mod 4 to $\mathrm{SL}(2,\mathbb{Z})$), which together with the Wang/Bockstein topological lemma yields phase $+1$ on every genus-1 $Q_8$-bundle!
6. Exact odd-$N$ counterexample theorem for all odd $N$ (and explicit `pushChain` check for $\mathrm{Dic}_3$): machine-checked normalized 3-cocycle $\omega_2^{\mathrm{odd}}$, $T_a^4$ relator/holonomy invariance, and 3-term bar 3-cycle pairing $= 1 \bmod 2$ (phase $-1$)!
