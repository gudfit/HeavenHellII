From Stdlib Require Import List Lia Arith PeanoNat Bool.
From HH.rinclude Require Import RulesHeavenHell.

Set Implicit Arguments.

Module Scale.

  Section Generic.
    Import HeavenHell.

    Variable V : Type.
    Variable dec : forall x y:V, {x=y}+{x<>y}.
    Variable allV : list V.
    Hypothesis Hnodup : NoDup allV.
    Hypothesis Hcomplete : forall v:V, In v allV.
    Variable w : V -> V -> nat.
    Variable g : V.
    Variable tau : V -> nat.

    (* ---------- Utilities and identities ---------- *)

    Definition total_in (v:V) : nat :=
      @sum_all V allV (fun u => w u v).

    Lemma ind_state_partition (y:State) :
      ind (state_eqb y Glory) + ind (state_eqb y Gnash) = 1.
    Proof. destruct y; cbn [state_eqb ind]; lia. Qed.

    (* Exact conservation: per-node inbound weight equals G-score + N-score. *)
    Lemma score_conservation : forall s v,
      @score V allV w (@force_g V dec g s) Glory v
      + @score V allV w (@force_g V dec g s) Gnash v
      = total_in v.
    Proof.
      intros s v.
      unfold total_in, score.
      rewrite <- (@sum_all_add V allV
                   (fun u => w u v * ind (state_eqb (@force_g V dec g s u) Glory))
                   (fun u => w u v * ind (state_eqb (@force_g V dec g s u) Gnash))).
      apply (@sum_all_ext V allV); intros u _.
      rewrite <- Nat.mul_add_distr_l, ind_state_partition; lia.
    Qed.

    Corollary scoreN_by_conservation : forall s v,
      @score V allV w (@force_g V dec g s) Gnash v
      = total_in v - @score V allV w (@force_g V dec g s) Glory v.
    Proof.
      intros s v.
      pose proof (score_conservation s v) as H.
      lia.
    Qed.

    Corollary rest_weight_total_decomp : forall v,
      total_in v = @hub_weight V w g v + @rest_weight V dec allV w g v.
    Proof.
      intro v; unfold total_in.
      apply (@total_weight_split V dec allV Hnodup Hcomplete w g v).
    Qed.

    (* Majority threshold characterization (ties -> Glory). *)
    Lemma next_heaven_tau_majority_form : forall s v,
      v <> g ->
      (@next_heaven_tau V dec allV w g tau s v = Glory
       <-> 2 * @score V allV w (@force_g V dec g s) Glory v + tau v >= total_in v).
    Proof.
      intros s v Hvg.
      set (SG := @score V allV w (@force_g V dec g s) Glory v).
      set (SN := @score V allV w (@force_g V dec g s) Gnash v).
      pose proof (score_conservation s v) as Hcons; cbv zeta in Hcons.
      pose proof (@next_heaven_tau_eq_Glory_iff_not_g V dec allV w g tau s v Hvg) as Hiff.
      split.
      - intro HG. apply Hiff in HG. rewrite <- Hcons. lia.
      - intro Hmaj. rewrite <- Hcons in Hmaj. apply Hiff. lia.
    Qed.

    (* ---------- Monotonicity in the state ---------- *)

    Definition state_le (s t : V -> State) : Prop :=
      forall u, s u = Glory -> t u = Glory.

    Lemma force_g_state_le s t :
      state_le s t -> state_le (@force_g V dec g s) (@force_g V dec g t).
    Proof.
      intros H u Hs.
      unfold force_g in *.
      destruct (dec u g) as [Eg|NE]; [reflexivity|].
      apply H. exact Hs.
    Qed.

    Lemma ind_true_le (b1 b2:bool) :
      (b1 = true -> b2 = true) -> ind b1 <= ind b2.
    Proof. intros Hb; destruct b1; cbn [ind]; [specialize (Hb eq_refl); destruct b2; cbn in *; try discriminate; lia|lia]. Qed.

    Lemma scoreG_monotone_state :
      forall s t v,
        state_le s t ->
        @score V allV w (@force_g V dec g s) Glory v
        <= @score V allV w (@force_g V dec g t) Glory v.
    Proof.
      intros s t v Hle.
      rewrite (@scoreG_split V dec allV Hnodup Hcomplete w g s v).
      rewrite (@scoreG_split V dec allV Hnodup Hcomplete w g t v).
      apply Nat.add_le_mono_l.
      eapply (@sum_all_le V allV). intros u _.
      destruct (dec u g) as [Eg|NE]; cbn; [lia|].
      destruct (s u) eqn:Su; destruct (t u) eqn:Tu; cbn.
      - lia.
      - (* s u = Glory, t u = Gnash contradicts state_le *)
        exfalso. specialize (Hle u). specialize (Hle Su). now rewrite Tu in Hle.
      - lia.
      - lia.
    Qed.

    Lemma scoreN_antitone_state :
      forall s t v,
        state_le s t ->
        @score V allV w (@force_g V dec g t) Gnash v
        <= @score V allV w (@force_g V dec g s) Gnash v.
    Proof.
      intros s t v Hle.
      rewrite (scoreN_by_conservation t v).
      rewrite (scoreN_by_conservation s v).
      set (SGs := @score V allV w (@force_g V dec g s) Glory v).
      set (SGt := @score V allV w (@force_g V dec g t) Glory v).
      (* Need: total - SGt <= total - SGs, which follows from SGs <= SGt. *)
      assert (Hcmp : SGs <= SGt).
      { unfold SGs, SGt. apply scoreG_monotone_state; exact Hle. }
      lia.
    Qed.

    Lemma next_heaven_tau_monotone_state :
      forall s t v,
        state_le s t ->
        @next_heaven_tau V dec allV w g tau s v = Glory ->
        @next_heaven_tau V dec allV w g tau t v = Glory.
    Proof.
      intros s t v Hle Hs.
      destruct (dec v g) as [Eg|NE].
      - (* v = g *)
        rewrite Eg in *. 
        rewrite (@next_heaven_tau_at_g V dec allV w g tau t).
        reflexivity.
      - (* v <> g *)
        pose proof (@next_heaven_tau_eq_Glory_iff_not_g V dec allV w g tau s v NE) as Hiff_s.
        pose proof (@next_heaven_tau_eq_Glory_iff_not_g V dec allV w g tau t v NE) as Hiff_t.
        apply Hiff_t.
        apply Hiff_s in Hs.
        (* SN_t <= SN_s and SG_s <= SG_t give the result. *)
        set (SGs := @score V allV w (@force_g V dec g s) Glory v).
        set (SNs := @score V allV w (@force_g V dec g s) Gnash v).
        set (SGt := @score V allV w (@force_g V dec g t) Glory v).
        set (SNt := @score V allV w (@force_g V dec g t) Gnash v).
        assert (H1 : SNt <= SNs) by (unfold SNt, SNs; apply scoreN_antitone_state; exact Hle).
        assert (H2 : SGs <= SGt) by (unfold SGs, SGt; apply scoreG_monotone_state; exact Hle).
        eapply Nat.le_trans; [apply H1|].
        eapply Nat.le_trans; [apply Hs|].
        apply Nat.add_le_mono_r; exact H2.
    Qed.

    (* ---------- Tie policy as a parameter ---------- *)

    Inductive TiePolicy := TieGlory | TieGnash | TieStay.

    Definition next_heaven_tau_policy (tp:TiePolicy) (s:V->State) (v:V) : State :=
      if dec v g then Glory else
      let s' := @force_g V dec g s in
      let SG := @score V allV w s' Glory v in
      let SN := @score V allV w s' Gnash  v in
      match tp with
      | TieGlory => if Nat.ltb (SG + tau v) SN then Gnash else Glory
      | TieGnash => if Nat.leb (SG + tau v) SN then Gnash else Glory
      | TieStay  => if Nat.ltb (SG + tau v) SN then Gnash else if Nat.ltb SN (SG + tau v) then Glory else s v
      end.

    Lemma next_heaven_tau_is_policy_Glory :
      forall s v, @next_heaven_tau V dec allV w g tau s v = next_heaven_tau_policy TieGlory s v.
    Proof. reflexivity. Qed.

    Lemma tie_gnash_characterization :
      forall s v, v <> g ->
        (next_heaven_tau_policy TieGnash s v = Glory <->
         @score V allV w (@force_g V dec g s) Gnash v < @score V allV w (@force_g V dec g s) Glory v + tau v).
    Proof.
      intros s v Hvg.
      unfold next_heaven_tau_policy.
      destruct (dec v g) as [|NE]; [contradiction|].
      set (s' := @force_g V dec g s).
      set (SG := @score V allV w s' Glory v).
      set (SN := @score V allV w s' Gnash v).
      split; intro H.
      - destruct (Nat.leb (SG + tau v) SN) eqn:Hb; [discriminate|].
        apply Nat.leb_nle in Hb. lia.
      - destruct (Nat.leb (SG + tau v) SN) eqn:Hb; [|reflexivity].
        apply Nat.leb_le in Hb. lia.
    Qed.

    Lemma tie_stay_glory_if_strict :
      forall s v, v <> g ->
        let s' := @force_g V dec g s in
        let SG := @score V allV w s' Glory v in
        let SN := @score V allV w s' Gnash  v in
        SN < SG + tau v -> next_heaven_tau_policy TieStay s v = Glory.
    Proof.
      intros s v Hvg s' SG SN Hlt.
      unfold next_heaven_tau_policy.
      destruct (dec v g) as [|NE]; [contradiction|].
      unfold s', SG, SN in *.
      set (T := @score V allV w (@force_g V dec g s) Glory v + tau v).
      set (R := @score V allV w (@force_g V dec g s) Gnash  v).
      destruct (Nat.ltb T R) eqn:E1.
      { apply Nat.ltb_lt in E1. exfalso; exact (Nat.lt_asymm _ _ E1 Hlt). }
      destruct (Nat.ltb R T) eqn:E2; [reflexivity|].
      apply Nat.ltb_ge in E2.
      exfalso.
      apply (Nat.lt_irrefl R).
      eapply Nat.lt_le_trans; [apply Hlt|exact E2].
    Qed.

    Lemma tie_stay_glory_if_tie_and_state_glory :
      forall s v, v <> g ->
        let s' := @force_g V dec g s in
        let SG := @score V allV w s' Glory v in
        let SN := @score V allV w s' Gnash  v in
        SN = SG + tau v -> s v = Glory -> next_heaven_tau_policy TieStay s v = Glory.
    Proof.
      intros s v Hvg s' SG SN Heq Hsv.
      unfold next_heaven_tau_policy.
      destruct (dec v g) as [|NE]; [contradiction|].
      set (T := @score V allV w (@force_g V dec g s) Glory v + tau v).
      set (R := @score V allV w (@force_g V dec g s) Gnash  v).
      assert (Hrt : R = T).
      { unfold R, T, s', SG, SN in *. exact Heq. }
      destruct (Nat.ltb T R) eqn:E1.
      { apply Nat.ltb_lt in E1. exfalso. rewrite Hrt in E1. now apply (Nat.lt_irrefl _) in E1. }
      destruct (Nat.ltb R T) eqn:E2.
      { reflexivity. }
      (* Both comparisons are false; the policy stays, so use Hsv. *)
      rewrite Hrt in E1, E2.
      rewrite Nat.ltb_irrefl in E1, E2.
      now rewrite Hsv.
    Qed.

    (* ---------- Sharper per-node caps (lightweight variant) ---------- *)

    (* A simple corollary of the existing bound: if k >= indeg_nonhub v,
       then rest_weight v <= k * max_in_nonhub v. *)
    Corollary rest_le_k_times_max_in_nonhub :
      forall v k,
        @indeg_nonhub V dec allV w g v <= k ->
        @rest_weight V dec allV w g v <= k * @max_in_nonhub V dec allV w g v.
    Proof.
      intros v k Hk.
      pose proof rest_le_indeg_times_max as Hbound.
      specialize (Hbound V dec allV Hcomplete w g v).
      eapply Nat.le_trans; [exact Hbound|].
      apply Nat.mul_le_mono_r; exact Hk.
    Qed.

    (* ---------- Asynchronous fairness: one-pass bound ---------- *)

    (* If a finite schedule covers all nonhubs at least once, one pass suffices. *)
    Lemma one_pass_covers_all_nonhubs_succeeds :
      (forall v, v <> g -> @hub_weight V w g v >= @rest_weight V dec allV w g v) ->
      forall sched s,
        (forall v, v <> g -> In v sched) ->
        forall v, v <> g ->
          @run_sched V dec allV w g s sched v = Glory.
    Proof.
      intros Hdom sched s Hcov v Hv.
      apply (@async_one_pass_all_G_nonhub V dec allV Hcomplete w g Hdom);
      [ exact Hcov | exact Hv ].
    Qed.

    (* ---------- Edge cases ---------- *)
    (* Notes:
       - nonhubs defaults to [] when all nodes are the hub; list_max [] = 0,
         so max-based bounds are vacuously true.
       - Zero-weight graphs satisfy all inequalities by reflexivity.
    *)

  End Generic.

End Scale.
