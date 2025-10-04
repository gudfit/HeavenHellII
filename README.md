# Heaven–Hell (Part II): Scaling Laws

This repo is a **mathematical**, Coq‑free companion to the `scale.v` / `scalelaw.v` results.
It contains a small Python simulator, along with paper-ready demos that **compute and exhibit** the scaling laws and tight thresholds for majority dynamics with a **pinned hub** under a **tie->Glory** update rule.

---

## TL;DR

* We study a weighted directed graph with a special **hub** `g` pinned to state **G** (Glory).
  Each non‑hub node updates by weighted majority with friction `tau(v)` and **ties break to G**.

* **One‑shot threshold (uniform hub):**
  If the hub sends weight `W` to every node, a worst‑case sufficient and necessary bound is
  [
  W^*(\tau) ;=; \max_{v\neq g}\max{0,,\text{rest_weight}(v)-\tau(v)},
  ]
  where `rest_weight(v)` sums all inbound weights to `v` **excluding** the hub.
  Examples: ring `k`‑nearest → `W* = 2k`; 4‑neighbor torus grid -> `W* = 4`.

* **Scaling law (d‑regular):** for (inbound) `d`‑regular families, **`W* = d`**.

* **Two‑step seeding:** with hub at `W = W* − 1`, seeding a small set `H` that satisfies a simple inequality (below) guarantees **all‑Glory after one synchronous step**.

* **Asynchronous one‑pass fairness:** if `hub_weight(v)+tau(v) ≥ rest_weight(v)` holds at every node, **any** one‑pass schedule that updates each node once yields all‑Glory.

* **Upper bound & gap:** the coarse bound
  `W* ≤ indeg_global × wmax_global` can be **very loose** (we show a 200× gap).

* **Multi‑hub additivity:** multiple hubs forced to G add linearly in the inequality; splitting the total budget `∑ W_i ≥ W*` succeeds in one step (with hubs pinned).

---

## Model (math only)

* **Graph:** finite set of nodes `V`, a special **hub** `g∈V`, directed weighted in‑edges `inbound[v] ⊆ V×ℕ`.
  States `s: V→{G,N}` with `s[g]=G` always (hub pinned).

* **Friction:** `tau: V→ℕ` (default 0).

* **Synchronous update (tie→Glory):** for each `v≠g`,

  * `SG(v) = Σ_{(u,w) in inbound[v]} [s(u)=G]·w  +  (hub term if u=g)`
  * `SN(v) = Σ_{(u,w) in inbound[v]} [s(u)=N]·w`
  * Next state: `s'(v)=G` iff `SG(v) + tau(v) ≥ SN(v)`; otherwise `N`.

* **Threshold with uniform hub weight:** if the hub adds the same weight `W` on the edge `(g→v)` for all `v≠g`, then a **worst‑case exact threshold** is
  [
  W^*(\tau)=\max_{v\neq g}\max{0,;\text{rest_weight}(v)-\tau(v)}
  ]
  where `rest_weight(v)=Σ_{(u,w)∈inbound[v], u≠g} w`.

* **Two‑step seeding inequality (sufficient):** for a proposed seed set `H⊆V\{g}`, define
  [
  \text{LHS}(v)=\text{hub_weight}(v)+\sum_{u\in H} w(u,v)+\tau(v), \qquad
  \text{RHS}(v)=\sum_{u\notin H\cup{g}} w(u,v).
  ]
  If `LHS(v) ≥ RHS(v)` holds for every `v≠g`, then after seeding `H` to G, **one synchronous step** yields **all‑Glory**, regardless of the initial state of non‑seeds.

---

## What the code shows (and how it maps to the claims)

Run the paper set:

```bash
python showcase.py --demo paper
```

### 1) Exact one‑shot thresholds on canonical families

* **Rings (`k`‑nearest):** `W* = 2k` (unit weights on the ring).
  We also show that **sub‑threshold** (`W=2k-1`) can succeed from *some* starts (e.g., checkerboard) — the theorem is worst‑case.
* **2D torus grid (4‑neighbor):** `W* = 4`.

**Scaling law (d‑regular):** for inbound `d`‑regular graphs, the runs report `W*≈d`, matching the analytic `W* = d`.

### 2) Phase diagrams with friction

* **Uniform friction:** `W*(t) = max(0, max_rest − t)` is monotone non‑increasing in `t`.
* **Heterogeneous friction:** `W*(τ) = max_v max(0, rest(v) − τ(v))`; the *argmax* nodes are the bottlenecks that control the threshold.

### 3) Two‑step seeding guarantees

* With `W = W*−1` on rings, periodic seed patterns with spacing `k` **certify** the two‑step inequality for all nodes; a sparser alternating `k/2k` pattern is also certified.
  (The greedy heuristic often finds even smaller sets, but the inequality is **sufficient, not necessary**.)

### 4) Asynchronous one‑pass fairness

* If `hub_weight(v)+tau(v) ≥ rest_weight(v)` for all `v≠g`, then **any** schedule that updates each node exactly once (hub pinned) ends in **all‑Glory**.
  We run several distinct orders, and all of them succeed.

### 5) Tightness (necessity) witness

* At `W = W*−1`, from the all‑Gnash state, there exists a node `v` with `next(v)=N`. The demo prints such a witness, showing the threshold is **tight**.

### 6) Community bottlenecks & degmax upper bound

* **Two cliques + weak bridge:** the bottlenecks are the two bridge endpoints.
  We verify the formula
  `rest(endpoint) = (n_i−1)·w_in + w_bridge`, others `(n_i−1)·w_in`.
  Thus, `W* = max_rest` occurs at the cut endpoints.
* **Degmax bound:** `W* ≤ indeg_global × wmax_global` can be **very loose**; we construct a 200× gap.

### 7) Multi‑hub budget split (additivity)

* With several hubs forced to G, contributions add:
  [
  \Big(\sum_i W_i\Big) + \tau(v) ;\ge; \text{rest_weight}(v) \quad \forall v
  \Longrightarrow \text{one‑step all‑Glory.}
  ]
  We demonstrate two and three hubs whose **sum budget** meets `W*`.

---

## Commands you will actually use

* Paper demos (comprehensive):

  ```bash
  python showcase.py --demo paper
  ```

* Compact demos (certified two‑step + multi‑hub splits):

  ```bash
  python showcase.py --demo all --n 60 --k 3
  ```

* Targeted:

  ```bash
  python showcase.py --demo two_step_ring   --n 60 --k 3
  python showcase.py --demo two_hub_split   --n 60 --k 3
  python showcase.py --demo three_hub_split --n 60 --k 3
  ```

**Dependencies:** Python 3.10+; no required external packages.
Optional: `matplotlib` for tiny plots in phase/margins demos.

---

## How to read the printed output

* `W*` lines report either **exact** values (via `max_rest` or `max_need_tau`) or **empirical** checks (random d‑regular‑like).
* “all‑Glory after one step = True/False” is an **actual simulation** under the pinned hub & tie→G rule.
* “Two‑step condition holds? …” uses the **sufficient** inequality. It may print `False` even when the dynamics succeed; that is expected.
* “Per‑node margins” show `hub_weight(v) + tau(v) − rest_weight(v)`; nonnegative margins certify domination.

---

## Mapping to `scale.v` and `scalelaw.v` (informal)

* **`scale.v` themes (realized here):**

  * Exact worst‑case one‑shot thresholds `W*(τ)` with pinned hub & tie→G.
  * Two‑step seeding condition and certified patterns on rings.
  * Asynchronous one‑pass fairness under the domination margins.
  * Tightness at `W*−1` via explicit witness states.

* **`scalelaw.v` themes (realized here):**

  * Scaling on structured families: rings (`W*=2k`), grids (`W*=4`), and `d`‑regular graphs (`W*=d`).
  * Upper/lower bounds: `W* = max_rest` vs the coarse `indeg_global × wmax_global` bound; explicit large‑gap example.
  * Community bottlenecks (two cliques + bridge) and analytic rest‑weight verification.
  * Multi‑hub budget **additivity**.

This Python is not a proof assistant; it **exhibits** the laws numerically and prints the exact inequalities your Coq development formalizes.

---

## Small helpers for the appendix

* `explain_node_update(sim, s, v, tau_map=None, forced=())`
  Prints `SG`, `SN`, `tau(v)`, `hub_weight`, `rest_weight`, and the decision at node `v`.
  Use it in counterexamples/multi‑hub runs to show the arithmetic at the witness.

* `exhaustive_uniform_hub_check(n, k)` (for small `n`)
  Certifies necessity at `W*=2k-1` (fails from all‑Gnash) and sufficiency at `W*=2k` (succeeds for all states).

---

## Limitations / Notes

* The two‑step check is **sufficient, not necessary**. Greedy seeds may succeed even when the inequality is not globally satisfied.
* Random “d‑regular‑like” graphs are sampled iid (not exactly d‑regular); we use them only as scaling evidence.
* For multi‑hub experiments, **pin** every hub to G (we use `next_state_forced`) to match the algebraic inequality.

---

## The story in one paragraph

We pin a single influencer (the hub) to Glory and ask: **how much weight suffices to flip the network in one shot, against a worst‑case adversary and with ties favoring Glory?** The answer is clean: **match the heaviest non‑hub inbound (`max_rest`) modulo friction**, giving the scaling laws `W*=2k` on rings, `4` on grids, and `d` on `d`‑regular families. When the budget is one unit short, a **small seed set** placed on a certified periodic pattern guarantees success in **one more step**. The same inequality applies to **asynchronous** one-pass schedules, and **multiple hubs** add their budgets. Coarse degree×weight bounds can be wildly pessimistic; the demos include a **200×** gap. The code prints the exact inequalities responsible for every conclusion.
