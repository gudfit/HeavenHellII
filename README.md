# Heaven & Hell (Part II): Scaling Laws

This is a **mathematical**, Coq‑free companion to the `scale.v` / `scalelaw.v` results.

---

## TL;DR

* **Graph + update:** Weighted digraph with a special **hub** $g$ pinned to state $G$.
  Non‑hub $v$ updates by weighted majority with friction $\tau(v)$ and **ties break to $G$**.

* **One‑shot threshold (uniform hub):** If the hub sends the same weight $W$ to all $v\ne g$,   

$$ W^*(\tau) = \max_{v\ne g}\max\\{0,\mathrm{rest_weight}(v)-\tau(v)\\}, $$ 
  
  where $\mathrm{rest_weight}(v)$ sums all inbound weights **excluding** the hub.
  Examples: ring $k$‑nearest $\Rightarrow W^\*=2k$; 4‑neighbor torus grid $\Rightarrow W^\*=4$.

* **Scaling law (d‑regular):** for inbound $d$‑regular families, $W^*=d$.

* **Two‑step seeding (sufficient):** with $W=W^\*-1$, any seed set $H$ that satisfies a simple per‑node inequality (below) guarantees **all‑Glory after one synchronous step**.

* **Asynchronous one‑pass fairness:** if $\mathrm{hub_weight}(v)+\tau(v)\ge \mathrm{rest_weight}(v)$ for all $v$, then **any** one‑pass schedule (each node updated once, hub pinned) yields all‑Glory.

* **Upper bound & gap:** the coarse bound $W^\*\le \mathrm{indeg_global}\cdot \mathrm{wmax_global}$ can be **very loose** (we show a $200\times$ gap).

* **Multi‑hub additivity:** with several pinned hubs, budgets add: $\sum_i W_i$ replaces $W$.

---

## Model

* **Graph:** finite $V$, special hub $g\in V$, directed weighted in‑edges $\mathrm{inbound}[v]\subseteq V\times \mathbb{N}$.
  States $s:V\to{G,N}$ with $s(g)=G$.

* **Friction:** $\tau:V\to\mathbb{N}$ (default $0$).

* **Synchronous update (tie->$G$):** for $v\ne g$,

$$
  \begin{aligned}
  S_G(v) &= \sum_{(u,w)\in \mathrm{inbound}[v]} \mathbf{1}[s(u)=G]\cdot w,\\
  S_N(v) &= \sum_{(u,w)\in \mathrm{inbound}[v]} \mathbf{1}[s(u)=N]\cdot w,\\
  s'(v) &= \begin{cases}
  G & \text{if } S_G(v)+\tau(v)\ge S_N(v),\\
  N & \text{otherwise.}
  \end{cases}
  \end{aligned}
  $$

* **Uniform hub threshold:** when every non‑hub receives the hub edge $(g!\to!v)$ with weight $W$,

$$ W^*(\tau)=\max_{v\ne g}\max\\{0,\mathrm{rest_weight}(v)-\tau(v)\\}, \mathrm{rest_weight}(v)= \sum_{\substack{(u,w)\in \mathrm{inbound}[v], u\ne g}} w.$$

* **Two‑step seeding (sufficient condition):** for $H\subseteq V\setminus{g}$ define

$$
  \mathrm{LHS}(v)=\mathrm{hub_weight}(v)+\sum_{u\in H} w(u,v)+\tau(v),\qquad
  \mathrm{RHS}(v)=\sum_{u\notin H\cup{g}} w(u,v).
  $$

  If $\mathrm{LHS}(v)\ge \mathrm{RHS}(v)$ for all $v\ne g$, then after seeding $H$ to $G$,
  **one synchronous step** yields **all‑Glory**, for any initial state of non‑seeds.

---

## What the code shows (and how it maps to the claims)

Run the paper set:

```bash
python showcase.py --demo paper
```

### 1) Exact one‑shot thresholds on canonical families

* **Rings ($k$‑nearest):** $W^*=2k$ (unit ring weights).
  Sub‑threshold ($W=2k-1$) can still succeed from *some* starts (checkerboard); the theorem is **worst‑case**.
* **2D torus grid (4‑neighbor):** $W^*=4$.

**Scaling law (d‑regular):** inbound $d$‑regular graphs report $W^\*\approx d$, matching the analytic $W^\*=d$.

### 2) Phase diagrams with friction

* **Uniform friction:** $W^*(t)=\max\\{0,\ \max_v \mathrm{rest_weight}(v)-t\\}$ is monotone non‑increasing in $t$.
* **Heterogeneous friction:** $W^*(\tau)=\max_v \max\\{0,\mathrm{rest_weight}(v)-\tau(v)\\}$; maximizers are the **bottlenecks**.

### 3) Two‑step seeding guarantees

With $W=W^*-1$ on rings, periodic seeds with spacing $k$ **certify** the inequality for all nodes; a sparser alternating $k/2k$ pattern is also certified.
(The greedy heuristic often finds even smaller sets; the inequality is **sufficient, not necessary**.)

### 4) Asynchronous one‑pass fairness

If $\mathrm{hub_weight}(v)+\tau(v)\ge \mathrm{rest_weight}(v)$ for all $v\ne g$, then **any** schedule that updates each node exactly once ends in **all‑Glory**.
We run several distinct orders; all succeed.

### 5) Tightness (necessity) witness

At $W=W^*-1$, from the all‑Gnash state there exists a node $v$ with $s'(v)=N$. The demo prints such a **witness**, showing the threshold is **tight**.

### 6) Community bottlenecks & degmax upper bound

* **Two cliques + weak bridge:** bottlenecks are the two bridge endpoints.
  For endpoints in clique $i$ (size $n_i$): $\mathrm{rest}=(n_i-1),w_{\mathrm{in}}+w_{\mathrm{bridge}}$;
  other nodes: $\mathrm{rest}=(n_i-1),w_{\mathrm{in}}$. Hence $W^*=\max\mathrm{rest}$ occurs at the cut endpoints.
* **Degmax bound:** $W^*\le \mathrm{indeg_global}\cdot \mathrm{wmax_global}$ can be **very** loose (we show a $200\times$ gap).

### 7) Multi‑hub budget split (additivity)

With several hubs pinned to $G$,

$$
\Big(\sum_i W_i\Big)+\tau(v) \ge \mathrm{rest_weight}(v)\quad\forall v \Rightarrow \text{one‑step all‑Glory}.
$$

Two and three‑hub demos split the budget so that $\sum_i W_i\ge W^*$ and succeed in one step.

---

## Commands

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
  python showcase.py --bench --bench-kind ring --n 10000 --k 3
  python showcase.py --bench --bench-kind grid --width 200 --height 200
  python showcase.py --bench --bench-kind scale-free --n 10000 --k 3 --seed 42
  python showcase.py --bench-scale --seed 42 

  ```

**Dependencies:** Python 3.10+; no required external packages.

### Benchmark CLI flags

  - --bench: run bench_suite instead of demos
  - --bench-kind ring|grid|scale-free, --width/--height for grids
  - --bench-scale: run the scalability plot harness
  - --seed to standardize randoms

Optional: `matplotlib`, `numpy`, `networkx` for small plots and benchmarks.

---

## How to read the printed output

* $W^\*$ lines are **exact** via $\max\mathrm{rest}$ or $\max\mathrm{need_tau}$, or **empirical** checks on sampled graphs.
* "all‑Glory after one step = True/False” is an **actual simulation** with hub pinned and tie-> $G$.
* "Two‑step condition holds?" uses the **sufficient** inequality; it may be `False` even when dynamics succeed (expected).
* "Per‑node margins” show $\mathrm{hub_weight}(v)+\tau(v)-\mathrm{rest_weight}(v)$; nonnegative margins certify domination.

---

## One‑paragraph story

We pin an influencer (the hub) to $G$ and ask: **how much weight suffices to flip the network in one shot, adversarially, with ties favoring $G$?** The answer is clean: **match the heaviest non‑hub inbound ($\max\mathrm{rest}$) modulo friction**, giving the scaling laws $W^\*=2k$ on rings, $4$ on grids, and $d$ on $d$‑regular families. With one unit less ($W^\*-1$), a small **certified seed set** yields success in **one more step**. The same inequality controls **asynchronous** one‑pass schedules, and **multiple hubs** simply add their budgets. Degree×weight bounds can be wildly pessimistic; the demos include a **$200\times$** gap. The code prints the exact inequalities behind each conclusion.

