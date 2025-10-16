from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Hashable, Iterable, List, Mapping, Tuple, Set


G = "G"  # Glory
N = "N"  # Gnash


@dataclass(frozen=True)
class Edge:
    src: Hashable
    dst: Hashable
    w: int


class MajorityHubSim:

    def __init__(
        self,
        nodes: Iterable[Hashable],
        inbound: Mapping[Hashable, List[Tuple[Hashable, int]]],
        g: Hashable,
        tau: Mapping[Hashable, int] | None = None,
    ) -> None:
        """Simulator for majority dynamics with a pinned hub and optional per-node tau."""
        self.nodes: Tuple[Hashable, ...] = tuple(nodes)
        self.g = g
        self.inbound: Dict[Hashable, List[Tuple[Hashable, int]]] = {
            v: list(inbound.get(v, [])) for v in self.nodes
        }
        self.tau: Dict[Hashable, int] = {v: 0 for v in self.nodes}
        if tau:
            for v, t in tau.items():
                self.tau[v] = int(t)
        # Lazy NumPy structures (built on first use)
        self._np_ready: bool = False
        self._nonhubs: Tuple[Hashable, ...] | None = None
        self._idx_of: Dict[Hashable, int] | None = None
        self._edge_src_idx = None
        self._edge_dst_idx = None
        self._edge_w = None
        self._rest_nonhub_arr = None
        self._hub_w_arr = None
        self._out_ptr = None
        self._out_dst = None
        self._out_w = None

    def hub_weight(self, v: Hashable) -> int:
        return sum(w for u, w in self.inbound.get(v, []) if u == self.g)

    def rest_weight(self, v: Hashable) -> int:
        return sum(w for u, w in self.inbound.get(v, []) if u != self.g)

    def max_rest(self) -> int:
        return max((self.rest_weight(v) for v in self.nodes if v != self.g), default=0)

    def w_from(self, H: Iterable[Hashable], v: Hashable) -> int:
        Hset = set(H)
        return sum(w for (u, w) in self.inbound.get(v, []) if u != self.g and u in Hset)

    def rest_outside(self, H: Iterable[Hashable], v: Hashable) -> int:
        Hset = set(H)
        return sum(
            w for (u, w) in self.inbound.get(v, []) if u != self.g and u not in Hset
        )

    def two_step_condition_holds(
        self, H: Iterable[Hashable], tau_map: Mapping[Hashable, int]
    ) -> bool:
        Hset = set(H)
        Hset.add(self.g)
        for v in self.nodes:
            if v == self.g:
                continue
            lhs = self.hub_weight(v) + self.w_from(Hset, v) + int(tau_map.get(v, 0))
            rhs = self.rest_outside(Hset, v)
            if lhs < rhs:
                return False
        return True

    def two_step_deficits(
        self, H: Iterable[Hashable], tau_map: Mapping[Hashable, int]
    ) -> Dict[Hashable, int]:
        """Return per-node shortfall: max(0, rhs - lhs). 0 means condition met."""
        Hset = set(H)
        Hset.add(self.g)
        deficits: Dict[Hashable, int] = {}
        for v in self.nodes:
            if v == self.g:
                continue
            lhs = self.hub_weight(v) + self.w_from(Hset, v) + int(tau_map.get(v, 0))
            rhs = self.rest_outside(Hset, v)
            deficits[v] = max(0, rhs - lhs)
        return deficits

    def greedy_seed(
        self,
        tau_map: Mapping[Hashable, int],
        H_init: Iterable[Hashable] | None = None,
        max_seeds: int | None = None,
        focus_only_deficit: bool = True,
    ) -> Tuple[List[Hashable], List[Tuple[Hashable, int]]]:
        """Greedy seed selection to satisfy the two-step condition."""
        # Fast NumPy path with vectorized gain computation (falls back if NumPy unavailable)
        try:
            import numpy as np  # type: ignore
            self._ensure_numpy()
            nonhubs = self._nonhubs  # type: ignore
            idx_of = self._idx_of  # type: ignore
            edge_src = self._edge_src_idx  # type: ignore
            edge_dst = self._edge_dst_idx  # type: ignore
            edge_w = self._edge_w  # type: ignore
            rest_arr = self._rest_nonhub_arr  # type: ignore
            hub_arr = self._hub_w_arr  # type: ignore

            H: List[Hashable] = list(H_init or [])
            Hset = set(H)
            history: List[Tuple[Hashable, int]] = []

            tau_arr = np.array([int(tau_map.get(v, 0)) for v in nonhubs], dtype=np.int64)
            n = len(nonhubs)

            seed_mask = np.zeros(n, dtype=bool)
            for u in Hset:
                if u == self.g:
                    continue
                j = idx_of.get(u)  # type: ignore
                if j is not None:
                    seed_mask[j] = True

            def compute_deficits(mask: np.ndarray) -> np.ndarray:
                if edge_src.size == 0:
                    seed_contrib = np.zeros(n, dtype=np.int64)
                else:
                    active = mask.astype(np.int64)
                    weights = edge_w * active[edge_src]
                    seed_contrib = np.bincount(edge_dst, weights=weights, minlength=n).astype(np.int64)
                lhs = hub_arr + tau_arr + seed_contrib
                d = (rest_arr - lhs)
                d[d < 0] = 0
                return d

            deficits = compute_deficits(seed_mask)
            if not np.any(deficits > 0):
                return H, history

            while True:
                if focus_only_deficit:
                    if edge_src.size == 0:
                        gain_by_src = np.zeros(n, dtype=np.int64)
                    else:
                        mask_edges = (deficits[edge_dst] > 0)
                        if mask_edges.any():
                            gain_by_src = np.bincount(edge_src[mask_edges], weights=edge_w[mask_edges], minlength=n).astype(np.int64)
                        else:
                            gain_by_src = np.zeros(n, dtype=np.int64)
                else:
                    if edge_src.size == 0:
                        gain_by_src = np.zeros(n, dtype=np.int64)
                    else:
                        gain_by_src = np.bincount(edge_src, weights=edge_w, minlength=n).astype(np.int64)

                # Exclude hub and already seeded
                cand_gain = gain_by_src.copy()
                cand_gain[seed_mask] = -1

                if cand_gain.size == 0:
                    break
                best_idx = int(np.argmax(cand_gain))
                best_gain = int(cand_gain[best_idx])

                if best_gain <= 0:
                    if np.any(deficits > 0):
                        print("[greedy_seed] No candidate improves deficit; inequality likely infeasible with remaining seeds.")
                    break

                best_u = nonhubs[best_idx]
                H.append(best_u)
                Hset.add(best_u)
                seed_mask[best_idx] = True
                history.append((best_u, best_gain))

                if max_seeds is not None and len(H) >= max_seeds:
                    break

                deficits = compute_deficits(seed_mask)
                if not np.any(deficits > 0):
                    break

            return H, history
        except Exception:
            # Fallback to original Python implementation
            H: List[Hashable] = list(H_init or [])
            Hset = set(H)
            history: List[Tuple[Hashable, int]] = []
            if self.two_step_condition_holds(H, tau_map):
                return H, history
            while True:
                deficits = self.two_step_deficits(H, tau_map)
                deficit_nodes = {v for v, d in deficits.items() if d > 0}
                if not deficit_nodes:
                    break
                best_u = None
                best_gain = -1
                for u in self.nodes:
                    if u == self.g or u in Hset:
                        continue
                    if focus_only_deficit:
                        gain = sum(
                            w for v in deficit_nodes for (src, w) in self.inbound.get(v, []) if src == u
                        )
                    else:
                        gain = sum(w for v in self.nodes if v != self.g for (src, w) in self.inbound.get(v, []) if src == u)
                    if gain > best_gain:
                        best_gain = gain
                        best_u = u
                if best_u is None or best_gain <= 0:
                    if any(d > 0 for d in deficits.values()):
                        print("[greedy_seed] No candidate improves deficit; inequality likely infeasible with remaining seeds.")
                    break
                H.append(best_u)
                Hset.add(best_u)
                history.append((best_u, best_gain))
                if max_seeds is not None and len(H) >= max_seeds:
                    break
                if self.two_step_condition_holds(H, tau_map):
                    break
            return H, history

    def apply_seed(self, s: Mapping[Hashable, str], H: Iterable[Hashable]) -> Dict[Hashable, str]:
        Hset = set(H)
        s2 = dict(s)
        for u in Hset:
            s2[u] = G
        s2[self.g] = G
        return s2

    def next_state(self, s: Mapping[Hashable, str], tau_override: Mapping[Hashable, int] | None = None) -> Dict[Hashable, str]:
        """Compute synchronous next state with pinned hub and tie->Glory.

        Directed inbound weights are used exactly as provided. The update is
        synchronous (one global step). For asynchronous behavior, use
        `run_schedule`, which applies `async_update` node-by-node.
        """
        s_next: Dict[Hashable, str] = {}
        for v in self.nodes:
            if v == self.g:
                s_next[v] = G
                continue
            tau_v = (self.tau if tau_override is None else tau_override).get(v, 0)
            SG = 0
            SN = 0
            for (u, w) in self.inbound.get(v, []):
                if u == self.g:
                    SG += w
                else:
                    if s[u] == G:
                        SG += w
                    else:
                        SN += w
            s_next[v] = G if SG + tau_v >= SN else N
        return s_next

    def next_state_forced(
        self,
        s: Mapping[Hashable, str],
        forced: Set[Hashable],
        tau_override: Mapping[Hashable, int] | None = None,
    ) -> Dict[Hashable, str]:
        """Synchronous next state with a set `forced` always treated as Glory (incl. g).

        Aligns with the MultiHub_Forced Coq model: every node in `forced ∪ {g}`
        is pinned to Glory for this update and also counted as Glory when
        contributing inbound weights.
        """
        forced = set(forced) | {self.g}
        s_next: Dict[Hashable, str] = {}
        tau_map = self.tau if tau_override is None else tau_override
        for v in self.nodes:
            if v in forced:
                s_next[v] = G
                continue
            SG = 0
            SN = 0
            for (u, w) in self.inbound.get(v, []):
                if u in forced or s.get(u, N) == G:
                    SG += w
                else:
                    SN += w
            t = int(tau_map.get(v, 0))
            s_next[v] = G if SG + t >= SN else N
        return s_next

    def run_one_step(self, s: Mapping[Hashable, str]) -> Dict[Hashable, str]:
        return self.next_state(s)

    def is_all_glory(self, s: Mapping[Hashable, str]) -> bool:
        return all((v == self.g or s[v] == G) for v in self.nodes)

    def need_tau(self, v: Hashable, tau_map: Mapping[Hashable, int]) -> int:
        if v == self.g:
            return 0
        r = self.rest_weight(v)
        t = int(tau_map.get(v, 0))
        return max(0, r - t)

    def max_need_tau(self, tau_map: Mapping[Hashable, int]) -> int:
        return max((self.need_tau(v, tau_map) for v in self.nodes if v != self.g), default=0)

    def argmax_need_tau(self, tau_map: Mapping[Hashable, int]) -> List[Hashable]:
        m = self.max_need_tau(tau_map)
        return [v for v in self.nodes if v != self.g and self.need_tau(v, tau_map) == m]

    def indeg_nonhub(self, v: Hashable) -> int:
        if v == self.g:
            return 0
        return sum(1 for (u, w) in self.inbound.get(v, []) if u != self.g and w > 0)

    def max_in_nonhub(self, v: Hashable) -> int:
        if v == self.g:
            return 0
        vals = [w for (u, w) in self.inbound.get(v, []) if u != self.g]
        return max(vals) if vals else 0

    def indeg_global(self) -> int:
        return max((self.indeg_nonhub(v) for v in self.nodes if v != self.g), default=0)

    def wmax_global(self) -> int:
        return max((self.max_in_nonhub(v) for v in self.nodes if v != self.g), default=0)

    def degmax_upper_bound(self) -> int:
        return self.indeg_global() * self.wmax_global()

    def degmax_pointwise_upper_bound(self) -> int:
        """Return max_v (indeg_nonhub(v) * max_in_nonhub(v)).

        This tightens the classical product bound indeg_global * wmax_global by
        taking the maximum of per-node products rather than multiplying two maxima
        that may be achieved at different vertices.
        """
        return max(
            (self.indeg_nonhub(v) * self.max_in_nonhub(v) for v in self.nodes if v != self.g),
            default=0,
        )

    def async_update(self, s: Mapping[Hashable, str], v: Hashable, tau_map: Mapping[Hashable, int] | None = None) -> Dict[Hashable, str]:
        """Update only node v using the same tie->Glory rule (hub forced G).

        This is the primitive for asynchronous schedules (`run_schedule`).
        """
        tau_map = tau_map or self.tau
        s_next = dict(s)
        if v == self.g:
            s_next[v] = G
            return s_next
        SG = 0
        SN = 0
        for (u, w) in self.inbound.get(v, []):
            if u == self.g:
                SG += w
            else:
                if s[u] == G:
                    SG += w
                else:
                    SN += w
        t = int(tau_map.get(v, 0))
        s_next[v] = G if SG + t >= SN else N
        s_next[self.g] = G
        return s_next

    def run_schedule(self, s: Mapping[Hashable, str], sched: Iterable[Hashable], tau_map: Mapping[Hashable, int] | None = None) -> Dict[Hashable, str]:
        # Fast incremental NumPy path (general graphs), fallback to Python version if unavailable
        try:
            import numpy as np  # type: ignore
            self._ensure_numpy()
            nonhubs = self._nonhubs  # type: ignore
            idx_of = self._idx_of  # type: ignore
            edge_src = self._edge_src_idx  # type: ignore
            edge_dst = self._edge_dst_idx  # type: ignore
            edge_w = self._edge_w  # type: ignore
            rest_arr = self._rest_nonhub_arr  # type: ignore
            hub_arr = self._hub_w_arr  # type: ignore
            out_ptr = self._out_ptr  # type: ignore
            out_dst = self._out_dst  # type: ignore
            out_w = self._out_w  # type: ignore

            n = len(nonhubs)
            x = np.zeros(n, dtype=np.int8)
            for i, v in enumerate(nonhubs):
                x[i] = 1 if s.get(v, N) == G else 0
            tmap_src = self.tau if tau_map is None else tau_map
            tarr = np.array([int(tmap_src.get(v, 0)) for v in nonhubs], dtype=np.int64)

            if edge_src.size == 0:
                sg_nonhub = np.zeros(n, dtype=np.int64)
            else:
                weights = (edge_w * x[edge_src]).astype(np.int64)
                sg_nonhub = np.bincount(edge_dst, weights=weights, minlength=n).astype(np.int64)

            sched_idx = [idx_of.get(v) for v in sched if v != self.g]  # type: ignore
            # Remove Nones silently
            sched_idx = [int(i) for i in sched_idx if i is not None]

            for vi in sched_idx:
                lhs = (sg_nonhub[vi] << 1) + hub_arr[vi] + tarr[vi]
                rhs = rest_arr[vi]
                new_state = 1 if lhs >= rhs else 0
                old_state = int(x[vi])
                if new_state != old_state:
                    delta = (1 if new_state == 1 else -1)
                    # Apply delta to all out-neighbors of vi
                    b = int(out_ptr[vi])
                    e = int(out_ptr[vi + 1])
                    if e > b:
                        dsts = out_dst[b:e]
                        wts = out_w[b:e]
                        # sg_nonhub[dst] += delta * w
                        # Use vectorized update
                        sg_nonhub[dsts] += (delta * wts)
                    x[vi] = new_state

            # Build result mapping
            st = {v: (G if x[idx_of[v]] == 1 else N) for v in nonhubs}  # type: ignore
            st[self.g] = G
            return st
        except Exception:
            st = dict(s)
            st[self.g] = G
            for v in sched:
                st = self.async_update(st, v, tau_map=tau_map)
            return st

    def run_schedule_forced(
        self,
        s: Mapping[Hashable, str],
        sched: Iterable[Hashable],
        forced: Set[Hashable],
        tau_map: Mapping[Hashable, int] | None = None,
    ) -> Dict[Hashable, str]:
        """Asynchronous one-pass with a set `forced` pinned to Glory throughout."""
        st = dict(s)
        forced = set(forced) | {self.g}
        for u in forced:
            st[u] = G
        tmap = self.tau if tau_map is None else tau_map
        for v in sched:
            if v in forced:
                st[v] = G
                continue
            SG = 0
            SN = 0
            for (u, w) in self.inbound.get(v, []):
                if u in forced or st.get(u, N) == G:
                    SG += w
                else:
                    SN += w
            st[v] = G if SG + int(tmap.get(v, 0)) >= SN else N
            for u in forced:
                st[u] = G
        return st

    def domination_condition_tau(self, tau_map: Mapping[Hashable, int]) -> bool:
        """Check hub_weight(v) + tau(v) >= rest_weight(v) for all non-hubs."""
        for v in self.nodes:
            if v == self.g:
                continue
            if self.hub_weight(v) + int(tau_map.get(v, 0)) < self.rest_weight(v):
                return False
        return True

    def per_node_margin_tau(self, tau_map: Mapping[Hashable, int]) -> Dict[Hashable, int]:
        """Return margin(v) = hub_weight(v) + tau(v) - rest_weight(v) (>=0 ensures success)."""
        margins: Dict[Hashable, int] = {}
        for v in self.nodes:
            if v == self.g:
                continue
            margins[v] = self.hub_weight(v) + int(tau_map.get(v, 0)) - self.rest_weight(v)
        return margins

    def _ensure_numpy(self) -> None:
        if self._np_ready:
            return
        import numpy as np  # type: ignore
        nonhubs = tuple(v for v in self.nodes if v != self.g)
        idx_of: Dict[Hashable, int] = {v: i for i, v in enumerate(nonhubs)}
        n = len(nonhubs)

        edge_src: List[int] = []
        edge_dst: List[int] = []
        edge_w: List[int] = []
        rest_arr = np.zeros(n, dtype=np.int64)
        hub_arr = np.zeros(n, dtype=np.int64)

        for v in nonhubs:
            vi = idx_of[v]
            for (u, w) in self.inbound.get(v, []):
                if u == self.g:
                    hub_arr[vi] += int(w)
                else:
                    ui = idx_of.get(u)
                    if ui is None:
                        continue
                    edge_src.append(int(ui))
                    edge_dst.append(int(vi))
                    edge_w.append(int(w))
                    rest_arr[vi] += int(w)

        edge_src_arr = np.array(edge_src, dtype=np.int32) if edge_src else np.zeros(0, dtype=np.int32)
        edge_dst_arr = np.array(edge_dst, dtype=np.int32) if edge_dst else np.zeros(0, dtype=np.int32)
        edge_w_arr = np.array(edge_w, dtype=np.int64) if edge_w else np.zeros(0, dtype=np.int64)

        # Build outbound CSR from edge lists
        counts = np.zeros(n, dtype=np.int64)
        if edge_src_arr.size:
            counts += np.bincount(edge_src_arr, minlength=n)
        out_ptr = np.zeros(n + 1, dtype=np.int64)
        np.cumsum(counts, out_ptr[1:])
        out_dst = np.zeros(edge_src_arr.size, dtype=np.int32)
        out_w = np.zeros(edge_src_arr.size, dtype=np.int64)
        if edge_src_arr.size:
            next_slot = out_ptr.copy()
            for e in range(edge_src_arr.size):
                u = edge_src_arr[e]
                i = next_slot[u]
                out_dst[i] = edge_dst_arr[e]
                out_w[i] = edge_w_arr[e]
                next_slot[u] += 1

        self._nonhubs = nonhubs
        self._idx_of = idx_of
        self._edge_src_idx = edge_src_arr
        self._edge_dst_idx = edge_dst_arr
        self._edge_w = edge_w_arr
        self._rest_nonhub_arr = rest_arr
        self._hub_w_arr = hub_arr
        self._out_ptr = out_ptr
        self._out_dst = out_dst
        self._out_w = out_w
        self._np_ready = True

    # --- Utilities for experiments and benchmarks ---
    def count_edges(self) -> int:
        return sum(len(self.inbound.get(v, [])) for v in self.nodes)

    def clone_with_hub_weights(self, by_v: Mapping[Hashable, int]) -> "MajorityHubSim":
        """Return a new simulator with hub inbound weights set per node v.

        This supports per-node exact sizing demos (non-uniform hub budgets).
        """
        inbound2: Dict[Hashable, List[Tuple[Hashable, int]]] = {
            v: [] for v in self.nodes
        }
        for v in self.nodes:
            for (u, w) in self.inbound.get(v, []):
                if u == self.g:
                    # drop existing g edge; we’ll reinsert below
                    continue
                inbound2[v].append((u, w))
        for v in self.nodes:
            if v == self.g:
                continue
            Wv = int(by_v.get(v, 0))
            if Wv > 0:
                inbound2[v].append((self.g, Wv))
        inbound2[self.g] = []
        return MajorityHubSim(self.nodes, inbound2, self.g, tau=self.tau)


def build_ring_with_hub(n: int, k: int = 1, W: int = 0, g: Hashable = "hub") -> MajorityHubSim:
    """Build a k-nearest neighbor ring C_n with a pinned hub."""
    assert n >= 2 and k >= 1 and k < n // 2 + (n % 2)
    nodes = list(range(n)) + [g]
    inbound: Dict[Hashable, List[Tuple[Hashable, int]]] = {v: [] for v in nodes}
    for v in range(n):
        for d in range(1, k + 1):
            inbound[v].append(((v - d) % n, 1))
            inbound[v].append(((v + d) % n, 1))
        if W > 0:
            inbound[v].append((g, W))
    inbound[g] = []
    return MajorityHubSim(nodes, inbound, g)


def build_grid_torus_with_hub(W: int = 0, width: int = 8, height: int = 8, g: Hashable = "hub") -> MajorityHubSim:
    """Build a 2D torus grid (`width` x `height`), 4-neighbors, unit weights, with a hub.

    Avoids shadowing the identifier `w` used elsewhere for weights by using
    `width` and `height` for clarity.
    """
    assert width >= 2 and height >= 2
    nodes: List[Hashable] = [(x, y) for y in range(height) for x in range(width)] + [g]
    inbound: Dict[Hashable, List[Tuple[Hashable, int]]] = {v: [] for v in nodes}
    for y in range(height):
        for x in range(width):
            v = (x, y)
            nbrs = [
                ((x - 1) % width, y),
                ((x + 1) % width, y),
                (x, (y - 1) % height),
                (x, (y + 1) % height),
            ]
            for u in nbrs:
                inbound[v].append((u, 1))
            if W > 0:
                inbound[v].append((g, W))
    inbound[g] = []
    return MajorityHubSim(nodes, inbound, g)


def build_random_d_regular_digraph(n: int, d: int, weight: int = 1, g: Hashable = "hub", seed: int | None = None) -> MajorityHubSim:
    """Build a simple random d-regular-like inbound structure (not strict regularity).

    If `seed` is provided, `random.seed(seed)` ensures reproducibility.
    """
    import random
    if seed is not None:
        random.seed(seed)
    assert 1 <= d < n
    nodes = list(range(n)) + [g]
    inbound: Dict[Hashable, List[Tuple[Hashable, int]]] = {v: [] for v in nodes}
    all_nonhub = list(range(n))
    for v in range(n):
        preds = random.sample([u for u in all_nonhub if u != v], k=d)
        for u in preds:
            inbound[v].append((u, weight))
    inbound[g] = []
    return MajorityHubSim(nodes, inbound, g)


def build_two_cliques_with_bridge(n1: int, n2: int, w_in: int = 3, w_bridge: int = 1, g: Hashable = "hub") -> MajorityHubSim:
    """Two dense cliques (complete digraphs without self-loops) bridged by a weak edge."""
    assert n1 >= 2 and n2 >= 2
    nodes = list(range(n1 + n2)) + [g]
    inbound: Dict[Hashable, List[Tuple[Hashable, int]]] = {v: [] for v in nodes}
    for v in range(n1):
        for u in range(n1):
            if u != v:
                inbound[v].append((u, w_in))
    for v in range(n1, n1 + n2):
        for u in range(n1, n1 + n2):
            if u != v:
                inbound[v].append((u, w_in))
    
    a_star = 0
    b_star = n1
    inbound[b_star].append((a_star, w_bridge))
    inbound[a_star].append((b_star, w_bridge))
    inbound[g] = []
    return MajorityHubSim(nodes, inbound, g)


def build_scale_free_with_hub(n: int, m: int = 2, W: int = 0, g: Hashable = "hub", seed: int | None = None) -> MajorityHubSim:
    """Build a scale-free (Barabási–Albert style) directed graph plus a hub.

    If networkx is available, use `barabasi_albert_graph` to create an undirected skeleton
    and convert to a directed inbound list by adding both directions (unit weights).
    Otherwise, fall back to a small custom preferential-attachment builder.
    """
    nodes = list(range(n)) + [g]
    inbound: Dict[Hashable, List[Tuple[Hashable, int]]] = {v: [] for v in nodes}
    if seed is not None:
        try:
            import random
            random.seed(seed)
        except Exception:
            pass
    used_networkx = False
    try:
        import networkx as nx  # type: ignore
        Gnx = nx.barabasi_albert_graph(n=n, m=max(1, m), seed=seed)
        for u, v in Gnx.edges():
            inbound[v].append((u, 1))
            inbound[u].append((v, 1))
        used_networkx = True
    except Exception:
        # Fallback: simple preferential attachment
        import random
        assert n >= max(3, m + 1)
        targets = list(range(m + 1))  # start with a clique of size m+1
        for v in range(m + 1):
            for u in range(m + 1):
                if u != v:
                    inbound[v].append((u, 1))
        degrees = [len(inbound[v]) for v in range(n)]
        for v in range(m + 1, n):
            # choose m distinct targets proportional to degree
            population = list(range(v))
            weights = [degrees[u] + 1 for u in population]
            preds = set()
            while len(preds) < m:
                preds.add(random.choices(population, weights=weights, k=1)[0])
            for u in preds:
                inbound[v].append((u, 1))
                inbound[u].append((v, 1))
                degrees[v] += 1
                degrees[u] += 1
    if W > 0:
        for v in range(n):
            inbound[v].append((g, W))
    inbound[g] = []
    return MajorityHubSim(nodes, inbound, g)


def checkerboard_ring(n: int) -> Dict[int, str]:
    return {i: (G if (i % 2 == 0) else N) for i in range(n)}


def checkerboard_grid(w: int, h: int) -> Dict[Tuple[int, int], str]:
    return {(x, y): (G if ((x + y) % 2 == 0) else N) for y in range(h) for x in range(w)}


def ascii_ring(s: Mapping[int, str]) -> str:
    return "".join("G" if s[i] == G else "N" for i in range(len(s)))


def ascii_grid(s: Mapping[Tuple[int, int], str], w: int, h: int) -> str:
    lines = []
    for y in range(h):
        line = []
        for x in range(w):
            line.append("G" if s[(x, y)] == G else "N")
        lines.append("".join(line))
    return "\n".join(lines)


def showcase_kill_checkerboard_ring(n: int = 20, k: int = 1) -> None:
    """Show the one-step kill on a checkerboard ring."""
    W_star = 2 * k
    
    sim_nohub = build_ring_with_hub(n=n, k=k, W=0)
    assert sim_nohub.max_rest() == W_star, (sim_nohub.max_rest(), W_star)

    
    sim = build_ring_with_hub(n=n, k=k, W=W_star)

    s0 = checkerboard_ring(n)
    print("Ring C_n checkerboard (k={}):".format(k))
    print("t=0:", ascii_ring(s0))
    s1 = sim.run_one_step({**s0, sim.g: G})
    print("t=1:", ascii_ring({i: s1[i] for i in range(n)}))
    print("Threshold predicted W*={}, used W={}.\n".format(W_star, W_star))


def showcase_kill_checkerboard_grid(w: int = 10, h: int = 6) -> None:
    """Show the one-step kill on a checkerboard 2D torus grid."""
    W_star = 4
    sim_nohub = build_grid_torus_with_hub(W=0, width=w, height=h)
    assert sim_nohub.max_rest() == W_star, (sim_nohub.max_rest(), W_star)

    sim = build_grid_torus_with_hub(W=W_star, width=w, height=h)
    s0 = checkerboard_grid(w, h)
    print("Grid {}x{} checkerboard:".format(w, h))
    print("t=0:\n" + ascii_grid(s0, w, h))
    s1 = sim.run_one_step({**s0, sim.g: G})
    print("t=1:\n" + ascii_grid({k: v for k, v in s1.items() if k != sim.g}, w, h))
    print("Threshold predicted W*={}, used W={}.\n".format(W_star, W_star))
    # Optional heatmap visualization
    try:
        import numpy as np  # type: ignore
        import matplotlib.pyplot as plt  # type: ignore
        def to_array(state: Mapping[Tuple[int, int], str]) -> "np.ndarray":
            arr = np.zeros((h, w), dtype=int)
            for y in range(h):
                for x in range(w):
                    arr[y, x] = 1 if state[(x, y)] == G else 0
            return arr
        a0 = to_array(s0)
        a1 = to_array({k: v for k, v in s1.items() if k != sim.g})
        fig, axes = plt.subplots(1, 2, figsize=(6, 3))
        im0 = axes[0].imshow(a0, cmap="Greens", vmin=0, vmax=1)
        axes[0].set_title("t=0 (G=1)")
        axes[0].axis("off")
        im1 = axes[1].imshow(a1, cmap="Greens", vmin=0, vmax=1)
        axes[1].set_title("t=1 (G=1)")
        axes[1].axis("off")
        fig.suptitle("Grid checkerboard kill (heatmaps)")
        fig.tight_layout()
        plt.show()
    except Exception:
        pass


def showcase_k_nearest_ring(n: int = 50, k: int = 3) -> None:
    """Demonstrate the W* = 2k threshold on a k-nearest ring."""
    W_star = 2 * k
    sim_nohub = build_ring_with_hub(n=n, k=k, W=0)
    assert sim_nohub.max_rest() == W_star

    s0 = checkerboard_ring(n)
    
    for W in (W_star - 1, W_star):
        sim = build_ring_with_hub(n=n, k=k, W=W)
        s1 = sim.run_one_step({**s0, sim.g: G})
        allG = sim.is_all_glory(s1)
        print(f"k-nearest ring (k={k}), W={W}: all-Glory after one step = {allG}")




def phase_uniform_tau_ring(n: int = 50, k: int = 3, t_max: int | None = None) -> None:
    """Compute and display W*(t) = max_v max(0, rest(v) - t) for uniform tau=t."""
    sim = build_ring_with_hub(n=n, k=k, W=0)
    max_rest = sim.max_rest()
    if t_max is None:
        t_max = max_rest + 3
    data: List[Tuple[int, int]] = []
    last = None
    for t in range(0, t_max + 1):
        tau = {v: t for v in sim.nodes}
        w_star = sim.max_need_tau(tau)
        data.append((t, w_star))
        if last is not None:
            assert w_star <= last, "tau_monotone violated (should be nonincreasing)"
        last = w_star
    print(f"Uniform tau on ring (n={n}, k={k}). max_rest={max_rest}.")
    print("t\tW*(t)")
    for t, w_star in data:
        print(f"{t}\t{w_star}")
    
    try:
        import matplotlib.pyplot as plt  # type: ignore

        ts = [t for t, _ in data]
        ws = [w for _, w in data]
        plt.figure(figsize=(4, 3))
        plt.step(ts, ws, where="post")
        plt.title(f"Phase: W* vs tau (ring k={k})")
        plt.xlabel("uniform tau")
        plt.ylabel("W* (min uniform hub weight)")
        plt.grid(True, alpha=0.3)
        plt.tight_layout()
        plt.show()
    except Exception:
        pass


def phase_uniform_tau_grid(w: int = 10, h: int = 8, t_max: int | None = None) -> None:
    """Uniform tau phase curve on 4-neighbor torus grid: W*(t) = max(0, 4 - t)."""
    sim = build_grid_torus_with_hub(W=0, width=w, height=h)
    max_rest = sim.max_rest()  
    if t_max is None:
        t_max = max_rest + 3
    data = []
    last = None
    for t in range(0, t_max + 1):
        tau = {v: t for v in sim.nodes}
        w_star = sim.max_need_tau(tau)
        data.append((t, w_star))
        if last is not None:
            assert w_star <= last
        last = w_star
    print(f"Uniform tau on grid ({w}x{h}). max_rest={max_rest}.")
    print("t\tW*(t)")
    for t, w_star in data:
        print(f"{t}\t{w_star}")
    try:
        import matplotlib.pyplot as plt  # type: ignore
        ts = [t for t, _ in data]
        ws = [w for _, w in data]
        plt.figure(figsize=(4, 3))
        plt.step(ts, ws, where="post")
        plt.title("Phase: W* vs tau (grid)")
        plt.xlabel("uniform tau")
        plt.ylabel("W* (min uniform hub weight)")
        plt.grid(True, alpha=0.3)
        plt.tight_layout()
        plt.show()
    except Exception:
        pass


def showcase_scaling_law_regular_topologies(seed: int | None = None) -> None:
    """d-regular families: ring, grid, and random d-regular digraphs."""
    import random
    if seed is not None:
        random.seed(seed)
    # Ring k-nearest: d = 2k
    print("-- Regular families --")
    for k in [1, 2, 3]:
        sim = build_ring_with_hub(n=60, k=k, W=0)
        d = sim.max_rest()  # should equal 2k
        tau = 0
        w_star = sim.max_need_tau({v: tau for v in sim.nodes})
        # Assertions to catch regressions: on k-nearest rings, d = 2k and W*(0) = 2k
        assert d == 2 * k, (d, 2 * k)
        assert w_star == 2 * k, (w_star, 2 * k)
        print(f"Ring: k={k}, degree d={d}, W* (tau=0)={w_star}")
    # Grid 4-neighbor: d = 4
    simg = build_grid_torus_with_hub(W=0, width=10, height=8)
    dg = simg.max_rest()
    w_star_g = simg.max_need_tau({v: 0 for v in simg.nodes})
    # Grid 4-neighbor torus: degree d = 4, W*(0) = 4
    assert dg == 4, (dg, 4)
    assert w_star_g == 4, (w_star_g, 4)
    print(f"Grid: d={dg}, W* (tau=0)={w_star_g}")
    
    for d in [3, 5]:
        simd = build_random_d_regular_digraph(n=80, d=d, seed=seed)
        w_star_d = simd.max_need_tau({v: 0 for v in simd.nodes})
        # In the builder each node has exactly d inbound unit-weight non-hub edges
        assert simd.max_rest() == d, (simd.max_rest(), d)
        assert w_star_d == d, (w_star_d, d)
        print(f"Random d-regular-like: d≈{d}, measured W*≈{w_star_d}")


def showcase_scaling_law_heterogeneous(n: int = 60, density: float = 0.05, max_w: int = 5, seed: int | None = None) -> None:
    """Heterogeneous weighted digraph: exact W* vs the degmax upper bound."""
    import random
    if seed is not None:
        random.seed(seed)
    nodes = list(range(n)) + ["hub"]
    g = "hub"
    inbound: Dict[Hashable, List[Tuple[Hashable, int]]] = {v: [] for v in nodes}
    for v in range(n):
        for u in range(n):
            if u == v:
                continue
            if random.random() < density:
                inbound[v].append((u, random.randint(1, max_w)))
    sim = MajorityHubSim(nodes, inbound, g)
    W_star = sim.max_rest()
    degmax_old = sim.degmax_upper_bound()
    degmax_pw = sim.degmax_pointwise_upper_bound()
    print("-- Heterogeneous weighted graph --")
    print(f"Exact W* = max_rest = {W_star}")
    equals = (degmax_pw == W_star)
    print(f"degmax_pointwise = {degmax_pw}  ({'exact' if equals else 'loose'})")
    print(f"old degmax = {degmax_old}")
    if degmax_old > 0:
        gap_old = degmax_old - W_star
        ratio_old = degmax_old / max(1, W_star)
        print(f"Old bound gap = {gap_old}, ratio = {ratio_old:.2f}x")
    if degmax_pw > 0:
        gap_pw = degmax_pw - W_star
        ratio_pw = degmax_pw / max(1, W_star)
        print(f"Pointwise bound gap = {gap_pw}, ratio = {ratio_pw:.2f}x")
    if degmax_pw > 0:
        improv = degmax_old / max(1, degmax_pw)
        print(f"Improvement factor over old bound: {improv:.2f}x tighter")


def showcase_scale_free_generalization(n: int = 200, m: int = 2, tau: int = 0, seed: int | None = None) -> None:
    """Show one-shot threshold behavior on scale-free graphs (heterogeneous degrees)."""
    sim = build_scale_free_with_hub(n=n, m=m, W=0, seed=seed)
    tau_map = {v: tau for v in sim.nodes}
    W_star = sim.max_need_tau(tau_map)
    print("-- Scale-free (BA) family --")
    print(f"n={n}, m={m}, tau={tau}, exact W*={W_star}")
    # Try just-below and at-threshold from all-Gnash
    if W_star > 0:
        sim_low = build_scale_free_with_hub(n=n, m=m, W=max(0, W_star - 1), seed=seed)
        s0 = {v: N for v in sim.nodes if v != sim.g}
        s1 = sim_low.next_state({**s0, sim_low.g: G}, tau_override=tau_map)
        print(" below threshold success?", sim_low.is_all_glory(s1))
    sim_at = build_scale_free_with_hub(n=n, m=m, W=W_star, seed=seed)
    s0 = {v: N for v in sim_at.nodes if v != sim_at.g}
    s1 = sim_at.next_state({**s0, sim_at.g: G}, tau_override=tau_map)
    print(" at threshold success?   ", sim_at.is_all_glory(s1))
    # Optional: quick NetworkX visualization of degree distribution if available
    try:
        import networkx as nx  # type: ignore
        import matplotlib.pyplot as plt  # type: ignore
        Gnx = nx.Graph()
        Gnx.add_nodes_from([v for v in sim.nodes if v != sim.g])
        for v in sim.nodes:
            if v == sim.g:
                continue
            for (u, w) in sim.inbound.get(v, []):
                if u != sim.g:
                    Gnx.add_edge(u, v)
        degs = [d for _, d in Gnx.degree()]
        plt.figure(figsize=(4, 3))
        plt.hist(degs, bins=30, alpha=0.7)
        plt.title("Scale-free degree distribution (non-hub)")
        plt.xlabel("degree")
        plt.ylabel("count")
        plt.tight_layout()
        plt.show()
    except Exception:
        pass


def showcase_per_node_exact_sizing_tau(n: int = 200, k: int = 3, tau_easy: int = 0, tau_hard: int = 5, frac_hard: float = 0.3, seed: int | None = None) -> None:
    """Heterogeneous tau and non-uniform hub weights sized exactly per node.

    - Build a k-nearest ring and assign two tau levels: hard (lower slack) and easy (higher slack).
    - Set hub inbound to each v as W(v) = max(0, rest_weight(v) - tau(v)).
    - By nonuniform_pointwise_sufficient, this yields one-step all Glory for any s.
    """
    import random
    if seed is not None:
        random.seed(seed)
    sim0 = build_ring_with_hub(n=n, k=k, W=0)
    nonhubs = [v for v in sim0.nodes if v != sim0.g and isinstance(v, int)]
    hard = set(random.sample(nonhubs, k=int(round(frac_hard * len(nonhubs)))))
    tau_map = {v: (tau_hard if v in hard else tau_easy) for v in sim0.nodes}
    W_by_v = {v: max(0, sim0.rest_weight(v) - int(tau_map.get(v, 0))) for v in sim0.nodes}
    sim = sim0.clone_with_hub_weights(W_by_v)
    # Verify domination pointwise
    assert sim.domination_condition_tau(tau_map)
    # Try random starts
    for t in range(3):
        s0 = {v: (G if random.random() < 0.5 else N) for v in nonhubs}
        s1 = sim.next_state({**s0, sim.g: G}, tau_override=tau_map)
        assert sim.is_all_glory(s1)
    print("-- Per-node exact sizing with heterogeneous tau --")
    print(f"ring n={n}, k={k}, |hard|={len(hard)}; success in one step for random starts.")




def explain_node_update(sim: MajorityHubSim,
                        s: Mapping[Hashable, str],
                        v: Hashable,
                        tau_map: Mapping[Hashable, int] | None = None,
                        forced: Iterable[Hashable] = ()) -> None:
    """Print SG, SN, hub_weight, rest_weight, tau(v), and the decision at node v."""
    tau_map = tau_map or sim.tau
    forced = set(forced) | {sim.g}
    SG = 0; SN = 0
    for (u, w) in sim.inbound.get(v, []):
        if u in forced or s.get(u, N) == G:
            SG += w
        else:
            SN += w
    print(f"v={v}   SG={SG}   SN={SN}   tau={tau_map.get(v,0)}   "
          f"hub_weight={sim.hub_weight(v)}   rest_weight={sim.rest_weight(v)}   "
          f"decision={'G' if SG + int(tau_map.get(v,0)) >= SN else 'N'}")


def exhaustive_uniform_hub_check(n: int, k: int) -> None:
    """Exhaustive over all 2^n initial states (small n) to verify:
       - For W >= 2k: one step -> all Glory, for *all* s
       - For W = 2k-1: there exists s with failure (we exhibit all-Gnash)
    """
    from itertools import product
    sim_at = lambda W: build_ring_with_hub(n=n, k=k, W=W)
    W_star = 2 * k

    
    sim_low = sim_at(W_star - 1)
    s_allN = {v: N for v in range(n)}
    s1 = sim_low.next_state({**s_allN, sim_low.g: G})
    assert not sim_low.is_all_glory(s1), "Below threshold unexpectedly succeeded"

    
    sim_star = sim_at(W_star)
    for bits in product([G, N], repeat=n):
        s = {i: bits[i] for i in range(n)}
        s1 = sim_star.next_state({**s, sim_star.g: G})
        assert sim_star.is_all_glory(s1), f"At threshold failed for s={bits}"
    print(f"[exhaustive check] ring n={n}, k={k} passed necessity & sufficiency.")


def assert_two_cliques_rest(sim: MajorityHubSim, n1: int, n2: int,
                            w_in: int, w_bridge: int) -> None:
    """Verify analytic rest weights in the two-clique + bridge graph."""
    a_star, b_star = 0, n1
    for v in range(n1):
        expected = (n1 - 1) * w_in + (w_bridge if v == a_star else 0)
        assert sim.rest_weight(v) == expected
    for v in range(n1, n1 + n2):
        expected = (n2 - 1) * w_in + (w_bridge if v == b_star else 0)
        assert sim.rest_weight(v) == expected


def showcase_scaling_law_community_graph(n1: int = 12, n2: int = 12, w_in: int = 3, w_bridge: int = 1) -> None:
    """Two-clique community graph: bottleneck nodes control the threshold."""
    sim = build_two_cliques_with_bridge(n1=n1, n2=n2, w_in=w_in, w_bridge=w_bridge)
    W_star = sim.max_rest()
    rest_vals = {v: sim.rest_weight(v) for v in sim.nodes if v != sim.g}
    max_nodes = [v for v, r in rest_vals.items() if r == W_star]
    print("-- Community graph (two cliques + weak bridge) --")
    print(f"W* = max_rest = {W_star}")
    print(f"Nodes achieving max_rest (bottleneck candidates): {max_nodes}")
    try:
        assert_two_cliques_rest(sim, n1=n1, n2=n2, w_in=w_in, w_bridge=w_bridge)
        print("rest_weight formula: verified")
    except AssertionError:
        print("rest_weight formula: verification FAILED")
    sample = list(range(min(6, n1))) + list(range(n1, n1 + min(6, n2)))
    print("rest_weight samples:")
    print(" ".join(f"{v}:{rest_vals[v]}" for v in sample))


def phase_heterogeneous_tau_two_communities(
    n: int = 60, k: int = 2, frac_hard: float = 0.3, tau_hard: int = 0, tau_easy: int = 5
) -> None:
    """Heterogeneous tau: one hard-to-flip community controls the threshold."""
    assert 0.0 < frac_hard < 1.0
    H = max(1, min(n - 1, int(round(frac_hard * n))))
    sim = build_ring_with_hub(n=n, k=k, W=0)
    tau = {v: (tau_hard if (isinstance(v, int) and v < H) else tau_easy) for v in sim.nodes}
    w_star = sim.max_need_tau(tau)
    argmax_nodes = sim.argmax_need_tau(tau)
    hard_set = set(range(H))
    hard_dominates = any((v in hard_set) for v in argmax_nodes if isinstance(v, int))
    print(f"Heterogeneous tau on ring (n={n}, k={k}). hard_fraction={frac_hard:.2f}")
    print(f"tau_hard={tau_hard}, tau_easy={tau_easy}")
    print(f"W* (tau) = {w_star}")
    print(f"Argmax nodes (sample up to 10): {argmax_nodes[:10]}")
    print("Controlling community:", "hard" if hard_dominates else "easy")
    # Audit pieces of the formula: max_rest and per-argmax need components
    max_rest = sim.max_rest()
    print(f"max_rest (tau=0) = {max_rest}")
    sample = argmax_nodes[:min(5, len(argmax_nodes))]
    details = []
    for v in sample:
        rv = sim.rest_weight(v)
        tv = int(tau.get(v, 0))
        need = max(0, rv - tv)
        details.append((v, rv, tv, need))
    if details:
        pieces = " ".join(f"v={v}: rest={rv}, tau={tv}, rest-tau={need}" for (v, rv, tv, need) in details)
        print("Argmax details:", pieces)

    s0 = checkerboard_ring(n)
    for W in [max(0, w_star - 1), w_star]:
        simW = build_ring_with_hub(n=n, k=k, W=W)
        s1 = simW.next_state({**s0, simW.g: G}, tau_override=tau)
        ok = simW.is_all_glory(s1)
        print(f"One-step all-Glory at W={W}? {ok}")


def showcase_greedy_seeding_two_step(
    n: int = 40, k: int = 2, W: int | None = None, tau: int = 0, max_seeds: int | None = 5
) -> None:
    """Start below one-step threshold; add a few seeds to guarantee two-step."""
    if W is None:
        W = max(0, 2 * k - 1)  
    sim = build_ring_with_hub(n=n, k=k, W=W)
    tau_map = {v: tau for v in sim.nodes}
    print(f"Greedy seeding on ring (n={n}, k={k}), W={W} < 2k={2*k}? {'YES' if W < 2*k else 'NO'}")
    s0 = checkerboard_ring(n)
    s1 = sim.run_one_step({**s0, sim.g: G})
    outcome = sim.is_all_glory(s1)
    print(f"One-step all-Glory without seeds = {outcome}")
    if W < 2 * k:
        print("  (Reminder: W*=2k is a worst-case guarantee; sub-threshold can still")
        print("   succeed from specific starts like checkerboard. The two-step check is")
        print("   sufficient, not necessary, so it may print False while dynamics succeed.)")

    H, hist = sim.greedy_seed(tau_map=tau_map, H_init=[], max_seeds=max_seeds)
    deficits = sim.two_step_deficits(H, tau_map)
    print(f"Selected seeds ({len(H)}): {H}")
    print("Two-step condition holds?", sim.two_step_condition_holds(H, tau_map))
    marks = ["G" if deficits[i] == 0 else "!" for i in range(n)]
    print("Per-node condition (G ok, ! deficit):")
    print("".join(marks))

    s_seeded = sim.apply_seed({**s0, sim.g: G}, H)
    s2 = sim.next_state(s_seeded, tau_override=tau_map)
    print("After seeding + one step, all-Glory?", sim.is_all_glory(s2))



from typing import Hashable as _Hashable  


def build_gap_graph(m: int = 120, M: int = 500, g: _Hashable = "hub") -> MajorityHubSim:
    """
    Adversarial graph with a huge gap between the degmax upper bound and the exact threshold.
    - Node 0: one heavy inbound edge of weight M from node 1  --> pushes wmax_global up to M.
    - Node 2: inbound from nodes 3..(m+2), each weight 1      --> pushes indeg_global up to m.
    Result:  max_rest ~ max(M, m)  but  indeg_global*wmax_global ~ m*M  >> max_rest.
    """
    n = m + 3
    nodes = list(range(n)) + [g]
    inbound: Dict[_Hashable, List[Tuple[_Hashable, int]]] = {v: [] for v in nodes}

    inbound[0].append((1, M))
    for u in range(3, m + 3):
        inbound[2].append((u, 1))

    inbound[1].append((0, 1))
    inbound[3].append((2, 1))
    inbound[g] = []
    return MajorityHubSim(nodes, inbound, g)


def showcase_degmax_gap_extreme(m: int = 120, M: int = 500) -> None:
    """Show an extreme gap between the degmax upper bound and exact W*."""
    sim = build_gap_graph(m=m, M=M)
    W_star = sim.max_rest()
    degmax_old = sim.degmax_upper_bound()
    degmax_pw = sim.degmax_pointwise_upper_bound()
    ratio_old = (degmax_old / max(1, W_star)) if W_star > 0 else float("inf")
    ratio_pw = (degmax_pw / max(1, W_star)) if W_star > 0 else float("inf")
    print("-- Extreme degmax gap example --")
    print(f"Parameters: m={m} (large indegree), M={M} (large max weight)")
    print(f"Exact W* = max_rest = {W_star}")
    equals = (degmax_pw == W_star)
    print(f"degmax_pointwise = {degmax_pw}  ({'exact' if equals else 'loose'})")
    print(f"old degmax = {degmax_old}")
    print(f"Ratio old/exact = {ratio_old:.2f}x; pointwise/exact = {ratio_pw:.2f}x")
    if degmax_pw > 0:
        improv = degmax_old / max(1, degmax_pw)
        print(f"Improvement factor over old bound: {improv:.2f}x tighter")


def build_ring_with_two_hubs(
    n: int,
    k: int,
    W_each: int,
    hubs: Tuple[_Hashable, _Hashable] = ("hub1", "hub2"),
) -> MajorityHubSim:
    """
    Ring C_n with two hubs h1,h2. Each hub contributes W_each into every non-hub.
    We return a MajorityHubSim with g=h1; h2 is just another node whose state we seed to G.
    """
    h1, h2 = hubs
    nodes = list(range(n)) + [h1, h2]
    inbound: Dict[_Hashable, List[Tuple[_Hashable, int]]] = {v: [] for v in nodes}
    for v in range(n):
        for d in range(1, k + 1):
            inbound[v].append(((v - d) % n, 1))
            inbound[v].append(((v + d) % n, 1))
        if W_each > 0:
            inbound[v].append((h1, W_each))
            inbound[v].append((h2, W_each))
    inbound[h1] = []
    inbound[h2] = []
    return MajorityHubSim(nodes, inbound, g=h1)


def showcase_multi_hub_budget_split(n: int = 60, k: int = 3) -> None:
    """
    Two hubs each with W_each = k on a k-nearest ring (so W* = 2k).
    - Single-hub with W=k can fail from all-Gnash (tight counterexample on rings).
    - Two hubs, each W=k, together succeed in one synchronous step from all-Gnash.
    """
    W_star = 2 * k
    W_each = k
    sim_single = build_ring_with_hub(n=n, k=k, W=W_each)
    s_allN = {v: N for v in range(n)}
    s1_single = sim_single.next_state({**s_allN, sim_single.g: G})
    ok_single = sim_single.is_all_glory(s1_single)
    print("-- Multi-hub budget split on ring --")
    print(f"Single hub: k={k}, W_each={W_each}, W*={W_star} -> all Glory from all-Gnash? {ok_single}")

    sim_two = build_ring_with_two_hubs(n=n, k=k, W_each=W_each, hubs=("h1", "h2"))
    s_seed = {**s_allN, "h1": G, "h2": G}
    s1_two = sim_two.next_state_forced(s_seed, forced={"h1", "h2"})
    ok_two = sim_two.is_all_glory(s1_two)
    print(f"Two hubs: each W={W_each} (sum=W*) -> all Glory from all-Gnash? {ok_two}")


def build_ring_with_three_hubs(
    n: int,
    k: int,
    W_each: Tuple[int, int, int],
    hubs: Tuple[_Hashable, _Hashable, _Hashable] = ("h1", "h2", "h3"),
) -> MajorityHubSim:
    """
    Ring C_n with three hubs h1,h2,h3. Each hub i contributes W_each[i] into every non-hub.
    We return a MajorityHubSim with g=h1; h2,h3 are regular nodes we will seed to G.
    """
    h1, h2, h3 = hubs
    w1, w2, w3 = W_each
    nodes = list(range(n)) + [h1, h2, h3]
    inbound: Dict[_Hashable, List[Tuple[_Hashable, int]]] = {v: [] for v in nodes}
    for v in range(n):
        for d in range(1, k + 1):
            inbound[v].append(((v - d) % n, 1))
            inbound[v].append(((v + d) % n, 1))
        if w1 > 0:
            inbound[v].append((h1, w1))
        if w2 > 0:
            inbound[v].append((h2, w2))
        if w3 > 0:
            inbound[v].append((h3, w3))
    inbound[h1] = []
    inbound[h2] = []
    inbound[h3] = []
    return MajorityHubSim(nodes, inbound, g=h1)


def showcase_three_hub_budget_split(n: int = 60, k: int = 3) -> None:
    """
    Three hubs splitting the exact one-shot budget on a k-nearest ring.
    Each hub gets at least floor(W*/3); we distribute the remainder so the sum is >= W*.
    All three hubs are seeded to G, showing one-shot success from all-Gnash.
    """
    W_star = 2 * k
    base = W_star // 3
    rem = W_star - 3 * base
    W_each = (base + (1 if 0 < rem else 0), base + (1 if 1 < rem else 0), base)
    total = sum(W_each)
    sim = build_ring_with_three_hubs(n=n, k=k, W_each=W_each, hubs=("h1", "h2", "h3"))
    s_allN = {v: N for v in range(n)}
    s_seed = {**s_allN, "h1": G, "h2": G, "h3": G}
    s1 = sim.next_state_forced(s_seed, forced={"h1", "h2", "h3"})
    ok = sim.is_all_glory(s1)
    print("-- Three-hub budget split on ring --")
    print(f"k={k}, W*={W_star}, split per hub = {W_each} (sum={total})")
    print(f"All Glory from all-Gnash with all three hubs seeded? {ok}")




def periodic_seed_cover_ring(
    n: int, k: int, offset: int = 0, spacing: int | None = None
) -> List[int]:
    """
    Periodic seed set on a k-nearest ring.
    For the two-step sufficient condition with W = 2k-1 and tau = 0 to hold
    for every node (including seeds), each node must have at least one other
    seed within distance <= k. The simple certified choice is spacing = k.

    spacing:
      - If None, defaults to spacing = k (certified).
      - You may pass a smaller spacing (<= k) to be even more conservative.
    """
    p = spacing if spacing is not None else k
    assert 1 <= p <= k, "For certified two-step inequality, require spacing <= k."
    return sorted({(offset + i) % n for i in range(0, n, p)})


def alternating_k_2k_seed_cover_ring(n: int, k: int, offset: int = 0) -> List[int]:
    """
    Optional: a sparser periodic-but-alternating pattern with gaps k, 2k, k, 2k, ...
    This satisfies the two constraints:
      (i) max gap <= 2k  (so every non-seed has a seeded neighbor within k), and
      (ii) no seed is flanked by two gaps > k  (so every seed has some seed within k).
    It reduces seed count relative to spacing=k (~ every 1.5k on average).
    """
    if 2 * k > n:
        return periodic_seed_cover_ring(n, k, offset=offset, spacing=k)
    pos = offset % n
    H = [pos]
    step = [k, 2 * k]
    i = 0
    while True:
        pos = (pos + step[i % 2]) % n
        if pos == H[0]:
            break
        H.append(pos)
        i += 1
    return sorted(set(H))


def showcase_two_step_minimal_seeds_ring(n: int = 60, k: int = 2) -> None:
    """
    Certified two-step guarantee with periodic seeds at spacing k when W = 2k-1, tau = 0.
    This guarantees the sufficient inequality holds for every node (worst-case start).
    Also prints an optional alternating k/2k pattern which is sparser but still certified.
    """
    W = 2 * k - 1
    sim = build_ring_with_hub(n=n, k=k, W=W)
    tau_map = {v: 0 for v in sim.nodes}

    H_k = periodic_seed_cover_ring(n, k, spacing=k)
    ok_k = sim.two_step_condition_holds(H_k, tau_map)
    H_alt = alternating_k_2k_seed_cover_ring(n, k)
    ok_alt = sim.two_step_condition_holds(H_alt, tau_map)

    print("-- Certified two-step seeds on ring --")
    print(f"n={n}, k={k}, W={W}")
    print(f" spacing=k:     |H|={len(H_k):>3} -> inequality holds? {ok_k}")
    print(f" alternating:   |H|={len(H_alt):>3} -> inequality holds? {ok_alt}")

    s0 = checkerboard_ring(n)
    for label, H in [("spacing=k", H_k), ("alternating", H_alt)]:
        s_seeded = sim.apply_seed({**s0, sim.g: G}, H)
        s1 = sim.next_state(s_seeded, tau_override=tau_map)
        print(f"  {label:11s} -> all Glory after seed+1 step? {sim.is_all_glory(s1)}")


def showcase_async_one_pass_fairness_ring(
    n: int = 40, k: int = 2, tau: int = 0, trials: int = 5, seed: int | None = None
) -> None:
    """Demonstrate that any one-pass schedule covering all non-hubs works."""
    import random
    if seed is not None:
        random.seed(seed)

    W = max(0, 2 * k - tau)
    sim = build_ring_with_hub(n=n, k=k, W=W)
    tau_map = {v: tau for v in sim.nodes}
    assert sim.domination_condition_tau(tau_map), "Domination condition must hold"

    nonhubs = [v for v in sim.nodes if v != sim.g and isinstance(v, int)]
    
    s0 = {v: (G if random.random() < 0.5 else N) for v in nonhubs}
    print(f"Async fairness on ring: n={n}, k={k}, tau={tau}, W={W}")
    ok_all = True
    for t in range(trials):
        order = nonhubs[:]
        random.shuffle(order)
        # One pass
        sT = sim.run_schedule({**s0, sim.g: G}, order, tau_map=tau_map)
        ok1 = sim.is_all_glory(sT)
        # Two and three passes (stability)
        sT2 = sim.run_schedule(sT, order, tau_map=tau_map)
        sT3 = sim.run_schedule(sT2, order, tau_map=tau_map)
        ok2 = sim.is_all_glory(sT2)
        ok3 = sim.is_all_glory(sT3)
        print(f" trial {t+1}: 1-pass={ok1}, 2-pass={ok2}, 3-pass={ok3}")
        ok_all = ok_all and ok1 and ok2 and ok3
    print("All trials succeeded?", ok_all)


def showcase_async_one_pass_fairness_grid(width: int = 8, height: int = 6, tau: int = 1, trials: int = 5, seed: int | None = None) -> None:
    """Same demonstration on a 2D torus grid with 4-neighbors."""
    import random
    if seed is not None:
        random.seed(seed)

    rest = 4
    W = max(0, rest - tau)
    sim = build_grid_torus_with_hub(W=W, width=width, height=height)
    tau_map = {v: tau for v in sim.nodes}
    assert sim.domination_condition_tau(tau_map)
    nonhubs = [(x, y) for y in range(height) for x in range(width)]
    s0 = {(x, y): (G if random.random() < 0.5 else N) for (x, y) in nonhubs}
    print(f"Async fairness on grid: {width}x{height}, tau={tau}, W={W}")
    ok_all = True
    for t in range(trials):
        order = nonhubs[:]
        random.shuffle(order)
        sT = sim.run_schedule({**s0, sim.g: G}, order, tau_map=tau_map)
        ok1 = sim.is_all_glory(sT)
        sT2 = sim.run_schedule(sT, order, tau_map=tau_map)
        sT3 = sim.run_schedule(sT2, order, tau_map=tau_map)
        ok2 = sim.is_all_glory(sT2)
        ok3 = sim.is_all_glory(sT3)
        print(f" trial {t+1}: 1-pass={ok1}, 2-pass={ok2}, 3-pass={ok3}")
        ok_all = ok_all and ok1 and ok2 and ok3
    print("All trials succeeded?", ok_all)


def showcase_async_three_schedules_ring(n: int = 30, k: int = 2, tau: int = 0, seed: int | None = None) -> None:
    """Run three very different one-pass schedules; all end Glory under domination."""
    import random
    if seed is not None:
        random.seed(seed)

    W = max(0, 2 * k - tau)
    sim = build_ring_with_hub(n=n, k=k, W=W)
    tau_map = {v: tau for v in sim.nodes}
    assert sim.domination_condition_tau(tau_map)
    nonhubs = [v for v in sim.nodes if v != sim.g and isinstance(v, int)]

    margins = sim.per_node_margin_tau(tau_map)
    print(f"Per-node margins (v: margin):")
    print(" ".join(f"{v}:{margins[v]}" for v in range(n)))

    s0 = {v: N for v in nonhubs}  
    schedules = [
        ("increasing", nonhubs[:]),
        ("reverse", list(reversed(nonhubs))),
        ("random", random.sample(nonhubs, k=len(nonhubs))),
    ]
    for name, order in schedules:
        sT = sim.run_schedule({**s0, sim.g: G}, order, tau_map=tau_map)
        ok = sim.is_all_glory(sT)
        print(f" schedule={name:10s} -> all Glory = {ok}")

    try:
        import matplotlib.pyplot as plt  # type: ignore

        xs = list(range(n))
        ys = [margins[i] for i in xs]
        plt.figure(figsize=(5, 2.5))
        plt.bar(xs, ys, color=["#2ca02c" if y >= 0 else "#d62728" for y in ys])
        plt.axhline(0, color="black", linewidth=1)
        plt.title("Domination margins (hub + tau − rest)")
        plt.xlabel("node")
        plt.ylabel("margin")
        plt.tight_layout()
        plt.show()
    except Exception:
        pass


def showcase_tight_counterexample_ring(n: int = 40, k: int = 2, tau: int = 0) -> None:
    """Exhibit a witness v when W < max_need_tau: next(all_gnash)[v] = Gnash."""
    sim0 = build_ring_with_hub(n=n, k=k, W=0)
    tau_map = {v: tau for v in sim0.nodes}
    W_star = sim0.max_need_tau(tau_map)
    print(f"Tight counterexample on ring (n={n}, k={k}, tau={tau})")
    print(f" max_need_tau W* = {W_star}")
    if W_star == 0:
        print(" Trivial regime: W* = 0, no counterexample below threshold.")
        return
    W = W_star - 1
    simW = build_ring_with_hub(n=n, k=k, W=W)
    argmax_nodes = sim0.argmax_need_tau(tau_map)
    witness = argmax_nodes[0]
    s0 = {v: N for v in range(n)}
    s1 = simW.next_state({**s0, simW.g: G}, tau_override=tau_map)
    result = s1[witness]
    print(f" choose W = W* - 1 = {W}; witness v={witness}; next(all_gnash)[v]={result}")
    print(" expected Gnash ->", result == N)


def assert_uniform_hub_threshold(sim: MajorityHubSim, tau_map: Mapping[Hashable, int]) -> None:
    """Smoke test: if the hub has uniform inbound edge weight W* into every non-hub,
    then for arbitrary initial states, one synchronous step yields all-Glory."""
    import random

    W_star = sim.max_need_tau(tau_map)

    def hub_uniform_Wstar() -> bool:
        for v in sim.nodes:
            if v == sim.g:
                continue
            w_from_g = [wt for (u, wt) in sim.inbound.get(v, []) if u == sim.g]
            if len(w_from_g) != 1 or w_from_g[0] != W_star:
                return False
        return True

    if not hub_uniform_Wstar():
        return

    nonhubs = [v for v in sim.nodes if v != sim.g]
    for _ in range(50):
        s0 = {v: (G if random.random() < 0.5 else N) for v in nonhubs}
        s1 = MajorityHubSim(sim.nodes, sim.inbound, sim.g).next_state({**s0, sim.g: G}, tau_override=tau_map)
        assert sim.is_all_glory(s1)


# --- benchmarks -------------------------------------------------------------- #
def bench_next_state(sim: MajorityHubSim, trials: int = 3) -> Tuple[float, float]:
    """Return (best_seconds, edges_per_second) for next_state on a random state."""
    import time, random
    nonhubs = [v for v in sim.nodes if v != sim.g]
    s = {v: (G if random.random() < 0.5 else N) for v in nonhubs}
    s[sim.g] = G
    m = sim.count_edges()
    best = float("inf")
    for _ in range(trials):
        t0 = time.perf_counter()
        _ = sim.next_state(s)
        t1 = time.perf_counter()
        best = min(best, t1 - t0)
    eps = (m / best) if best > 0 else float("inf")
    return best, eps


def bench_two_step(sim: MajorityHubSim, H: Iterable[Hashable] | None = None, trials: int = 3) -> Tuple[float, float]:
    """Return (best_seconds, edges_per_second) for two_step_condition_holds."""
    import time
    H = list(H or [])
    tau = {v: 0 for v in sim.nodes}
    m = sim.count_edges()
    best = float("inf")
    for _ in range(trials):
        t0 = time.perf_counter()
        _ = sim.two_step_condition_holds(H, tau)
        t1 = time.perf_counter()
        best = min(best, t1 - t0)
    eps = (m / best) if best > 0 else float("inf")
    return best, eps


def bench_run_schedule(sim: MajorityHubSim, trials: int = 3) -> Tuple[float, float]:
    """Return (best_seconds, edges_per_second) for a full async pass over non-hubs."""
    import time, random
    nonhubs = [v for v in sim.nodes if v != sim.g]
    s = {v: (G if random.random() < 0.5 else N) for v in nonhubs}
    s[sim.g] = G
    sched = list(nonhubs)
    m = sim.count_edges()
    best = float("inf")
    for _ in range(trials):
        random.shuffle(sched)
        t0 = time.perf_counter()
        _ = sim.run_schedule(s, sched)
        t1 = time.perf_counter()
        best = min(best, t1 - t0)
    eps = (m / best) if best > 0 else float("inf")
    return best, eps


def bench_suite(kind: str = "ring", n: int = 10_000, k: int = 3, width: int = 200, height: int = 200, seed: int | None = None) -> None:
    if kind == "ring":
        sim = build_ring_with_hub(n=n, k=k, W=2 * k)
        print(f"[graph] ring n={n}, k={k}, edges≈{sim.count_edges()}")
    elif kind == "grid":
        sim = build_grid_torus_with_hub(W=4, width=width, height=height)
        print(f"[graph] grid {width}x{height}, edges≈{sim.count_edges()}")
    elif kind == "scale-free":
        sim = build_scale_free_with_hub(n=n, m=max(1, k), W=max(1, 2 * k), seed=seed)
        print(f"[graph] scale-free n={n}, m={k}, edges≈{sim.count_edges()}")
    else:
        raise ValueError("kind must be 'ring', 'grid', or 'scale-free'")

    b, eps = bench_next_state(sim)
    print(f"[bench] next_state: best={b:.4f}s, {eps:,.0f} edges/s")
    b, eps = bench_two_step(sim)
    print(f"[bench] two_step_condition: best={b:.4f}s, {eps:,.0f} edges/s")
    b, eps = bench_run_schedule(sim)
    print(f"[bench] run_schedule (one pass): best={b:.4f}s, {eps:,.0f} edges/s")


def benchmark_scalability(
    ks: List[int] | None = None,
    ns: List[int] | None = None,
    trials: int = 5,
    seed: int | None = None,
) -> None:
    """Benchmark key operations on rings across n and k, with log-log plots."""
    import time
    try:
        import matplotlib.pyplot as plt  # type: ignore
    except Exception:
        plt = None  # type: ignore
    ks = ks or [1, 2, 3]
    ns = ns or [100, 500, 1000, 5000, 10_000]
    results: Dict[str, List[float]] = {"greedy_seed": [], "next_state": [], "run_schedule": []}
    labels = list(results.keys())
    for n in ns:
        times = {op: [] for op in labels}
        for _ in range(trials):
            for k in ks:
                sim = build_ring_with_hub(n=n, k=k, W=max(1, 2 * k - 1))
                tau_map = {v: 0 for v in sim.nodes}
                s0 = {v: (G if ((isinstance(v, int) and (v % 2 == 0)) or v == sim.g) else N) for v in sim.nodes}
                # greedy_seed
                t0 = time.perf_counter()
                sim.greedy_seed(tau_map=tau_map, max_seeds=max(1, n // 20))
                times["greedy_seed"].append(time.perf_counter() - t0)
                # next_state
                t0 = time.perf_counter()
                _ = sim.next_state(s0, tau_override=tau_map)
                times["next_state"].append(time.perf_counter() - t0)
                # run_schedule
                sched = [v for v in sim.nodes if v != sim.g]
                t0 = time.perf_counter()
                _ = sim.run_schedule(s0, sched, tau_map=tau_map)
                times["run_schedule"].append(time.perf_counter() - t0)
        for op in labels:
            avg = sum(times[op]) / (trials * len(ks))
            results[op].append(avg)
            print(f"n={n:>6}, op={op:12s}: avg time={avg:.4f}s over {trials} trials, ks={ks}")
    if plt is not None:
        plt.figure(figsize=(8, 5))
        for op in labels:
            plt.plot(ns, results[op], marker='o', label=op)
        plt.title("Runtime Scaling (Rings, Multi-k)")
        plt.xlabel("n (nodes)")
        plt.ylabel("Avg Time (s)")
        plt.xscale("log")
        plt.yscale("log")
        plt.grid(True, alpha=0.3)
        plt.legend()
        plt.tight_layout()
        plt.show()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Heaven-Hell showcase runner")
    parser.add_argument(
        "--demo",
        choices=[
            "all",                
            "paper",              
            "two_step_ring",
            "two_hub_split",
            "three_hub_split",
        ],
        default="all",
        help="Which showcase to run (default: all)",
    )
    parser.add_argument("--n", type=int, default=60, help="ring size for ring demos")
    parser.add_argument("--k", type=int, default=3, help="k-nearest parameter for ring demos")
    parser.add_argument("--seed", type=int, default=None, help="random seed for demos/benchmarks")
    # Benchmark flags
    parser.add_argument("--bench", action="store_true", help="run benchmarks instead of demos")
    parser.add_argument("--bench-kind", choices=["ring", "grid", "scale-free"], default="ring")
    parser.add_argument("--width", type=int, default=200, help="grid width for bench")
    parser.add_argument("--height", type=int, default=200, help="grid height for bench")
    parser.add_argument("--bench-scale", action="store_true", help="run scaling benchmark suite with plots")
    args = parser.parse_args()

    if args.bench:
        bench_suite(kind=args.bench_kind, n=args.n, k=args.k, width=args.width, height=args.height, seed=args.seed)
        raise SystemExit(0)
    if args.bench_scale:
        benchmark_scalability(seed=args.seed)
        raise SystemExit(0)

    if args.demo in ("all", "two_step_ring"):
        showcase_two_step_minimal_seeds_ring(n=args.n, k=max(2, args.k))

    if args.demo in ("all", "two_hub_split"):
        showcase_multi_hub_budget_split(n=args.n, k=args.k)

    if args.demo in ("all", "three_hub_split"):
        showcase_three_hub_budget_split(n=args.n, k=args.k)

    if args.demo == "paper":
        showcase_kill_checkerboard_ring(n=20, k=1)
        showcase_kill_checkerboard_grid(w=10, h=6)
        showcase_k_nearest_ring(n=max(10, args.n), k=args.k)
        phase_uniform_tau_ring(n=args.n, k=args.k)
        phase_heterogeneous_tau_two_communities(n=args.n, k=args.k, frac_hard=0.33, tau_hard=0, tau_easy=5)
        showcase_greedy_seeding_two_step(n=40, k=max(2, args.k), W=2*max(2, args.k)-1, tau=0, max_seeds=4)
        showcase_async_one_pass_fairness_ring(n=args.n, k=args.k, tau=0, trials=3)
        showcase_async_one_pass_fairness_grid(width=8, height=6, tau=1, trials=3)
        showcase_async_three_schedules_ring(n=30, k=args.k, tau=0)
        showcase_tight_counterexample_ring(n=40, k=args.k, tau=0)
        phase_uniform_tau_grid(w=10, h=8)
        showcase_scaling_law_regular_topologies()
        showcase_scaling_law_heterogeneous(n=80, density=0.06, max_w=7)
        showcase_scale_free_generalization(n=200, m=2, tau=0, seed=args.seed)
        showcase_per_node_exact_sizing_tau(n=120, k=args.k, tau_easy=0, tau_hard=5, frac_hard=0.33, seed=args.seed)
        showcase_scaling_law_community_graph(n1=12, n2=12, w_in=3, w_bridge=1)
        showcase_degmax_gap_extreme(m=200, M=800)
        showcase_multi_hub_budget_split(n=args.n, k=args.k)
        showcase_three_hub_budget_split(n=args.n, k=args.k)
