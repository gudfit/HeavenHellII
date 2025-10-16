import random, statistics, csv
from pathlib import Path
import matplotlib.pyplot as plt
import matplotlib as mpl

Glory, Gnash = 1, 0

try:
    sbm_two_community
except NameError:

    def sbm_two_community(
        n1: int, n2: int, p_in: float, p_out: float, wmin: int = 1, wmax: int = 2
    ):
        n = n1 + n2
        w = [[0 for _ in range(n)] for _ in range(n)]
        import random

        for u in range(n):
            for v in range(n):
                if u == v:
                    continue
                same = (u < n1 and v < n1) or (u >= n1 and v >= n1)
                p = p_in if same else p_out
                if random.random() < p:
                    w[u][v] = random.randint(wmin, wmax)
        return w


try:
    JamEvent
except NameError:

    class JamEvent:
        def __init__(self, start: int, end: int, targets, scale: float):
            self.start, self.end, self.targets, self.scale = (
                start,
                end,
                list(targets),
                scale,
            )
            self.active = False
            self.original = {}

        def apply(self, t, w, g):
            if self.start <= t < self.end and not self.active:
                self.active = True
                self.original = {v: w[g][v] for v in self.targets}
                for v in self.targets:
                    w[g][v] = int(round(self.scale * w[g][v]))
            elif (t >= self.end) and self.active:
                for v, val in self.original.items():
                    w[g][v] = val
                self.active = False


try:
    MisinfoEvent
except NameError:

    class MisinfoEvent:
        def __init__(self, start: int, end: int, stubborn):
            self.start, self.end, self.stubborn = start, end, set(stubborn)

        def stubborn_set(self, t):
            return self.stubborn if (self.start <= t < self.end) else set()


try:
    MisinfoAmplifyEvent
except NameError:

    class MisinfoAmplifyEvent:
        def __init__(self, start: int, end: int, stubborn, scale: float):
            self.start, self.end, self.stubborn, self.scale = (
                start,
                end,
                set(stubborn),
                scale,
            )
            self.active = False
            self.original = {}

        def apply(self, t, w):
            n = len(w)
            if (t >= self.end) and self.active:
                for (u, v), val in self.original.items():
                    w[u][v] = val
                self.original = {}
                self.active = False
            if self.start <= t < self.end and not self.active:
                self.active = True
                self.original = {}
                for u in self.stubborn:
                    for v in range(n):
                        if w[u][v] > 0:
                            self.original[(u, v)] = w[u][v]
                            w[u][v] = int(round(self.scale * w[u][v]))


try:
    EdgeOutageProcess
except NameError:

    class EdgeOutageProcess:
        def __init__(self, start: int, end: int, fraction: float):
            self.start, self.end, self.fraction = start, end, fraction
            self.prev = []
            self.active = False

        def apply(self, t, w):
            n = len(w)
            if self.prev:
                for u, v, oldw in self.prev:
                    w[u][v] = oldw
                self.prev = []
            if self.start <= t < self.end:
                edges = [(u, v) for u in range(n) for v in range(n) if w[u][v] > 0]
                k = int(round(self.fraction * len(edges)))
                if k > 0 and edges:
                    import random

                    picks = random.sample(edges, min(k, len(edges)))
                    for u, v in picks:
                        self.prev.append((u, v, w[u][v]))
                        w[u][v] = 0


def inbound_list(w):
    n = len(w)
    inb = [[] for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if w[u][v] > 0:
                inb[v].append(u)
    return inb


def add_uniform_hub(w, g, W):
    n = len(w)
    for v in range(n):
        if v == g:
            continue
        w[g][v] = W


def add_nonuniform_hub(w, g, Wv):
    n = len(w)
    for v in range(n):
        if v == g:
            continue
        w[g][v] = int(Wv[v])


def rest_weight_fast(w, inb, g, v):
    return sum(w[u][v] for u in inb[v] if u != g)


def max_need_tau_fast(w, inb, g, tau):
    n = len(w)
    best_v = -1
    best_val = -(10**9)
    for v in range(n):
        if v == g:
            continue
        val = rest_weight_fast(w, inb, g, v) - tau[v]
        if val > best_val:
            best_val, best_v = val, v
    return best_val, best_v


def argmax_set_fast(w, inb, g, tau):
    mx, _ = max_need_tau_fast(w, inb, g, tau)
    n = len(w)
    return [
        v
        for v in range(n)
        if v != g and (rest_weight_fast(w, inb, g, v) - tau[v] == mx)
    ]


def compute_need_scores_fast(w, inb, g, tau):
    n = len(w)
    arr = []
    for v in range(n):
        if v == g:
            continue
        arr.append((v, rest_weight_fast(w, inb, g, v) - tau[v]))
    arr.sort(key=lambda x: x[1], reverse=True)
    return arr


def attack_contribution_index_fast(w, inb, g, tau, u):
    base, _ = max_need_tau_fast(w, inb, g, tau)
    n = len(w)
    best_val = -(10**9)
    for v in range(n):
        if v == g:
            continue
        new_rest = rest_weight_fast(w, inb, g, v) - (w[u][v] if u != g else 0)
        val = new_rest - tau[v]
        if val > best_val:
            best_val = val
    return base - best_val


def top_aci_fast(w, inb, g, tau, k=6):
    n = len(w)
    scores = [
        (u, attack_contribution_index_fast(w, inb, g, tau, u))
        for u in range(n)
        if u != g
    ]
    scores.sort(key=lambda x: x[1], reverse=True)
    return scores[:k]


def tie_decision(SG, SN, tau_v, current, policy):
    if policy == "glory":
        return Glory if SG + tau_v >= SN else Gnash
    if policy == "gnash":
        return Glory if SG + tau_v > SN else Gnash
    if policy == "stay":
        if SG + tau_v > SN:
            return Glory
        if SG + tau_v < SN:
            return Gnash
        return current
    raise ValueError


def next_fast(w, inb, g, tau, s, v, seeds, policy):
    if v == g or (v in seeds):
        return Glory
    SG = SN = 0
    for u in inb[v]:
        su = Glory if (u == g or u in seeds) else s[u]
        if su == Glory:
            SG += w[u][v]
        else:
            SN += w[u][v]
    return tie_decision(SG, SN, tau[v], s[v], policy)


def run_one_pass_fast(w, inb, g, tau, s, seeds, policy, schedule):
    s = s[:]
    for v in schedule:
        s[v] = next_fast(w, inb, g, tau, s, v, seeds, policy)
    return s


def fraction_glory(s, exclude=set()):
    c = n = 0
    for i, si in enumerate(s):
        if i in exclude:
            continue
        n += 1
        c += 1 if si == Glory else 0
    return c / max(1, n)


def simulate_fast(
    w,
    inb,
    g,
    tau,
    seeds,
    policy="glory",
    T=80,
    init_state="checker",
    jam_events=None,
    misinfo_events=None,
    mis_amp_events=None,
    outage_processes=None,
    schedule_mode="random",
    clamp_misinfo=True,
):
    import random

    n = len(w)
    # init
    if init_state == "all_gnash":
        s = [Gnash] * n
    elif init_state == "checker":
        s = [Glory if (i % 2 == 0) else Gnash for i in range(n)]
    elif init_state.startswith("random_"):
        try:
            p = float(init_state.split("_")[1])
        except:
            p = 0.5
        s = [Glory if random.random() < p else Gnash for _ in range(n)]
    else:
        s = [Gnash] * n

    def force_visible(s):
        sv = s[:]
        for u in seeds.union({g}):
            sv[u] = Glory
        return sv

    series_frac = []
    series_consensus = []
    time_to_all = None
    recovery = None
    firstD = None
    lastD = None
    jam_events = jam_events or []
    misinfo_events = misinfo_events or []
    mis_amp_events = mis_amp_events or []
    outage_processes = outage_processes or []

    def any_active(t):
        return (
            any(ev.start <= t < ev.end for ev in jam_events)
            or any(ev.start <= t < ev.end for ev in misinfo_events)
            or any(op.start <= t < op.end for op in outage_processes)
            or any(ev.start <= t < ev.end for ev in mis_amp_events)
        )

    for t in range(T):
        for op in outage_processes:
            op.apply(t, w)
        for ev in jam_events:
            ev.apply(t, w, g)
        for amp in mis_amp_events:
            amp.apply(t, w)

        if schedule_mode == "random":
            schedule = list(range(n))
            random.shuffle(schedule)
        elif schedule_mode == "increasing":
            schedule = list(range(n))
        elif schedule_mode == "reverse":
            schedule = list(range(n - 1, -1, -1))
        elif schedule_mode in (
            "priority_bottleneck_first",
            "adversarial_bottleneck_last",
        ):
            needs = compute_need_scores_fast(w, inb, g, tau)
            order = [v for v, _ in needs]
            schedule = (
                order
                if schedule_mode == "priority_bottleneck_first"
                else list(reversed(order))
            )
            schedule.append(g)
        else:
            schedule = list(range(n))
            random.shuffle(schedule)

        s = run_one_pass_fast(w, inb, g, tau, s, seeds, policy, schedule)

        if clamp_misinfo:
            stubborn = set()
            for ev in misinfo_events:
                stubborn |= ev.stubborn_set(t)
            for u in stubborn:
                if u != g and (u not in seeds):
                    s[u] = Gnash

        sv = force_visible(s)
        series_frac.append(fraction_glory(sv))
        series_consensus.append(all(x == Glory for x in sv))

        if any_active(t) and firstD is None:
            firstD = t
        if any_active(t):
            lastD = t
        if time_to_all is None and series_consensus[-1]:
            time_to_all = t

    if lastD is not None:
        for tt in range(lastD, T):
            if series_consensus[tt]:
                recovery = tt - lastD
                break

    return {
        "series_frac": series_frac,
        "series_consensus": series_consensus,
        "time_to_all_glory": time_to_all,
        "recovery_time": recovery,
        "first_disrupt_t": firstD,
        "last_disrupt_t": lastD,
    }


def build_mission_profile_500(profile="short_intense", seed=0):
    random.seed(seed)
    n1 = n2 = 250
    n = n1 + n2
    w = sbm_two_community(n1, n2, p_in=0.05, p_out=0.008, wmin=1, wmax=3)
    inb = inbound_list(w)
    g = 0
    tau = [0] * n
    T = 80
    start = 30
    A = argmax_set_fast(w, inb, g, tau)
    if not A:
        A = list(range(1, n))
    jam_k = max(20, len(A) // 10)
    jam_targets = random.sample(A, min(jam_k, len(A)))
    if profile == "short_intense":
        jam = JamEvent(start, start + 6, jam_targets, scale=0.0)
    else:
        jam = JamEvent(start, start + 24, jam_targets, scale=0.4)

    mis_targets = random.sample(list(range(n1, n)), max(1, n // 10))
    mis = MisinfoEvent(
        start, start + 10 if profile == "short_intense" else start + 24, mis_targets
    )
    amp = MisinfoAmplifyEvent(
        start,
        start + 10 if profile == "short_intense" else start + 24,
        mis_targets,
        scale=1.8,
    )

    outage = EdgeOutageProcess(
        start, (start + 8 if profile == "short_intense" else start + 24), fraction=0.03
    )

    Wstar, _ = max_need_tau_fast(w, inb, g, tau)
    w_uniform = [row[:] for row in w]
    add_uniform_hub(w_uniform, g, Wstar)
    inb_uniform = inbound_list(w_uniform)
    need_sorted = compute_need_scores_fast(w, inb, g, tau)
    top2 = [v for v, _ in need_sorted[: max(1, n // 50)]]
    Wv = [Wstar] * n
    for v in top2:
        Wv[v] = Wstar + 2
    w_nonuni = [row[:] for row in w]
    add_nonuniform_hub(w_nonuni, g, Wv)
    inb_nonuni = inbound_list(w_nonuni)

    aci_top = top_aci_fast(w_uniform, inb_uniform, g, tau, k=8)
    seeds = set(u for u, _ in aci_top[:8])

    events = {
        "jam_events": [jam],
        "misinfo_events": [mis],
        "mis_amp_events": [amp],
        "outage_processes": [outage],
    }

    return {
        "base": {"w": w, "inb": inb, "g": g, "tau": tau, "T": T},
        "uniform": {"w": w_uniform, "inb": inb_uniform},
        "nonuniform": {"w": w_nonuni, "inb": inb_nonuni, "boosted_targets": top2},
        "events": events,
        "aci_top_uniform": aci_top,
        "W_star": Wstar,
    }


def evaluate_side_by_side(profile="short_intense", trials=3, R=12, seed=0, plot=True):
    base_dir = Path(__file__).parent
    csv_dir = base_dir / "csv"
    csv_dir.mkdir(parents=True, exist_ok=True)

    try:
        plt.style.use("seaborn-v0_8-darkgrid")
    except Exception:
        try:
            plt.style.use("seaborn-darkgrid")
        except Exception:
            plt.style.use("ggplot")
    mpl.rcParams.update(
        {
            "axes.titlesize": 12,
            "axes.labelsize": 11,
            "legend.fontsize": 9,
            "xtick.labelsize": 10,
            "ytick.labelsize": 10,
            "axes.grid": True,
            "grid.alpha": 0.3,
            "figure.dpi": 200,
        }
    )
    mp = build_mission_profile_500(profile=profile, seed=seed)
    g = mp["base"]["g"]
    tau = mp["base"]["tau"]
    T = mp["base"]["T"]
    variants = []
    for budget in ["uniform", "nonuniform"]:
        for seeding in ["no_seeds", "with_seeds"]:
            for sched in ["priority_bottleneck_first", "adversarial_bottleneck_last"]:
                variants.append((budget, seeding, sched))

    seeds_set = set(u for u, _ in mp["aci_top_uniform"][:8])

    summaries = []
    series_curves = {}
    for budget, seeding, sched in variants:
        key = f"{budget}|{seeding}|{sched}"
        w0 = [row[:] for row in mp[budget]["w"]]
        inb0 = [lst[:] for lst in mp[budget]["inb"]]
        jam_events = [
            JamEvent(ev.start, ev.end, ev.targets, ev.scale)
            for ev in mp["events"]["jam_events"]
        ]
        mis_events = [
            MisinfoEvent(ev.start, ev.end, list(ev.stubborn))
            for ev in mp["events"]["misinfo_events"]
        ]
        amp_events = [
            MisinfoAmplifyEvent(ev.start, ev.end, list(ev.stubborn), ev.scale)
            for ev in mp["events"]["mis_amp_events"]
        ]
        outage_processes = [
            EdgeOutageProcess(op.start, op.end, op.fraction)
            for op in mp["events"]["outage_processes"]
        ]
        series_sum = [0.0] * T
        dips = []
        times = []
        recs = []
        rows_csv = []
        for tr in range(trials):
            w_tr = [row[:] for row in w0]
            inb_tr = inb0
            jam = [
                JamEvent(ev.start, ev.end, list(ev.targets), ev.scale)
                for ev in mp["events"]["jam_events"]
            ]
            mis = [
                MisinfoEvent(ev.start, ev.end, list(ev.stubborn))
                for ev in mp["events"]["misinfo_events"]
            ]
            amp = [
                MisinfoAmplifyEvent(ev.start, ev.end, list(ev.stubborn), ev.scale)
                for ev in mp["events"]["mis_amp_events"]
            ]
            out = [
                EdgeOutageProcess(op.start, op.end, op.fraction)
                for op in mp["events"]["outage_processes"]
            ]
            seeds_now = set() if seeding == "no_seeds" else set(seeds_set)
            res = simulate_fast(
                w=w_tr,
                inb=inb_tr,
                g=g,
                tau=tau[:],
                seeds=seeds_now,
                policy="glory",
                T=T,
                init_state="checker",
                jam_events=jam,
                misinfo_events=mis,
                mis_amp_events=amp,
                outage_processes=out,
                schedule_mode=sched,
                clamp_misinfo=True,
            )
            sf = res["series_frac"]
            for t in range(T):
                series_sum[t] += sf[t]
            dips.append(min(sf))
            times.append(
                res["time_to_all_glory"] if res["time_to_all_glory"] is not None else -1
            )
            recs.append(
                1
                if (res["recovery_time"] is not None and res["recovery_time"] <= R)
                else 0
            )
            rows_csv.append(
                {
                    "trial": tr,
                    "dip_min_fraction_glory": min(sf),
                    "time_to_all_glory": res["time_to_all_glory"],
                    "recovery_time_after_disruption": res["recovery_time"],
                }
            )
        series_avg = [x / trials for x in series_sum]
        RCS = sum(recs) / trials
        median_time = (
            statistics.median([x for x in times if x >= 0])
            if any(x >= 0 for x in times)
            else None
        )
        series_curves[key] = series_avg
        summaries.append(
            {
                "variant": key,
                "RCS": RCS,
                "avg_min_dip": sum(dips) / len(dips),
                "median_time_to_all_glory": median_time,
            }
        )
        csv_filename = f"Mission500_{profile}_{budget}_{seeding}_{sched}.csv"
        csv_path_fs = csv_dir / csv_filename
        with open(csv_path_fs, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=list(rows_csv[0].keys()))
            writer.writeheader()
            writer.writerows(rows_csv)
        summaries[-1]["csv"] = f"./csv/{csv_filename}"

    if plot:
        plt.figure(figsize=(10, 6))
        for key, y in series_curves.items():
            plt.plot(y, label=key, linewidth=2)
        plt.title(f"MissionProfile500 ({profile}) — Avg fraction Glory")
        plt.xlabel("time step")
        plt.ylabel("fraction Glory")
        plt.legend(
            title="Variant",
            loc="center left",
            bbox_to_anchor=(1.02, 0.5),
            frameon=False,
        )
        plt.tight_layout()
        png_path = base_dir / f"Mission500_{profile}_curves.png"
        plt.savefig(png_path, dpi=200, bbox_inches="tight")
        plt.show()

    sum_filename = f"Mission500_{profile}_summary.csv"
    sum_path_fs = csv_dir / sum_filename
    with open(sum_path_fs, "w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "variant",
                "RCS",
                "avg_min_dip",
                "median_time_to_all_glory",
                "csv",
            ],
        )
        writer.writeheader()
        writer.writerows(summaries)

    return {
        "profile": profile,
        "W_star": mp["W_star"],
        "aci_top_uniform": mp["aci_top_uniform"],
        "boosted_targets_nonuniform": mp["nonuniform"]["boosted_targets"],
        "summary": summaries,
        "summary_csv": f"./csv/{sum_filename}",
    }


out_short = evaluate_side_by_side(
    profile="short_intense", trials=3, R=12, seed=0, plot=True
)
out_long = evaluate_side_by_side(
    profile="long_partial", trials=3, R=20, seed=1, plot=True
)

out_short, out_long
