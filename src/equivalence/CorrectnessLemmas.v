From Stdlib Require Import String ZArith Reals List.
Import ListNotations.
Open Scope string_scope.

From OCL.equivalence Require Import Models Utils.
From OCL.equivalence Require Import OCLSyntax OCLSemantic.
From OCL.equivalence Require Import RASyntax RASemantic.
From OCL.equivalence Require Import Translation. 

From Stdlib Require Import Permutation.
From Stdlib Require Import Program.Equality.










(**
  Lemma combine_singleton

  结构等式：
  -------------------------
  将两个单元素列表做 combine，
  等价于生成一个单元素 pair 列表。

      combine [a] [b] = [(a,b)]

  ----------------------------------------
  语义意义

  这是 combine 在最小非空输入上的规范行为。

*)
Lemma combine_singleton :
  forall (A B : Type) (a : A) (b : B),
    combine [a] [b] = [(a,b)].
Proof. reflexivity. Qed.



(**
  Lemma lookup_row_single

  单元素行查找的规范行为。

  ----------------------------------------
  语义说明

  对只包含一列的行：

      [(c', v)]

  在列 c 上做 lookup 的结果是：

      Some v   若 c = c'
      None     若 c ≠ c'

  即：

      lookup_row c [(c', v)]
      = if c =? c' then Some v else None

  这个 lemma 给出了 lookup_row 在最小输入上的精确规格，
  是后续行语义推理中的基础 rewrite 规则。

*)
Lemma lookup_row_single :
  forall (c c' : ColName) (v : I_ra),
    lookup_row c [(c', v)] = if c =? c' then Some v else None.
Proof.
  intros. simpl. destruct (string_dec c' c) as [Heq | Hneq].
- subst.
  (* 目标变成: Some v = if c =? c then Some v else None *)
  rewrite String.eqb_refl.
  reflexivity.
- (* c' <> c *)
  (* 目标: None = if c =? c' then Some v else None *)
  assert (Hneq' : c <> c').
  { intro Hcc'. apply Hneq. now symmetry. }
  (* 用 eqb_neq 得到 c =? c' = false *)
  apply String.eqb_neq in Hneq'.
  rewrite Hneq'.
  reflexivity.
Qed.












Lemma select_rowsF_in_true :
  forall evalRex cond rows1 rows2 r,
    select_rowsF evalRex cond rows1 = Some rows2 ->
    In r rows2 ->
    In r rows1 /\
    evalRex r cond = Some (Ira_Bool true).
Proof.
  intros evalRex cond rows1.
  induction rows1 as [|x xs IH]; intros rows2 r Hsel Hin.
  - simpl in Hsel. inversion Hsel; subst rows2. contradiction.
  - simpl in Hsel.
    destruct (evalRex x cond) as [vc|] eqn:Hc; try discriminate.
    destruct vc; try discriminate.
    destruct b.
    + (* true: keep x *)
      destruct (select_rowsF evalRex cond xs) as [out|] eqn:Hrec; try discriminate.
      inversion Hsel; subst rows2; clear Hsel.
      simpl in Hin.
      destruct Hin as [-> | Hin'].
      * split; [left; reflexivity | exact Hc].
      * destruct (IH out r eq_refl Hin') as [Hin_xs Hr_true].
      split.
      -- right. exact Hin_xs.
      -- exact Hr_true.

    + (* false: drop x *)
      destruct (select_rowsF evalRex cond xs) as [out|] eqn:Hrec; try discriminate.
      inversion Hsel; subst rows2; clear Hsel.
      destruct (IH out r eq_refl Hin) as [Hin_xs Htrue].
      split.
      -- right. exact Hin_xs.
      -- exact Htrue.

Qed.








Lemma select_rowsF_in :
  forall (evalRex : RowData -> rex -> option I_ra)
         (cond : rex) (rows out : list RowData) (r : RowData),
    select_rowsF evalRex cond rows = Some out ->
    In r out ->
    In r rows /\ evalRex r cond = Some (Ira_Bool true).
Proof.
  intros evalRex cond rows.
  induction rows as [|a rs IH]; intros out r Hsel Hin.
  - simpl in Hsel. inversion Hsel. subst out. contradiction.
  - simpl in Hsel.
    destruct (evalRex a cond) eqn:Ha; try discriminate.
    destruct i; try discriminate.
    destruct b.
    + destruct (select_rowsF evalRex cond rs) eqn:Hrs; try discriminate.
      inversion Hsel; subst out.
      simpl in Hin. destruct Hin as [->|Hin'].
      * split; [left; reflexivity| exact Ha].
      * specialize (IH l r eq_refl Hin') as [Hin_rs Hev].
        split.
        -- right; exact Hin_rs.
        -- exact Hev.
    + destruct (select_rowsF evalRex cond rs) eqn:Hrs; try discriminate.
      inversion Hsel; subst out.
      specialize (IH l r eq_refl Hin) as [Hin_rs Hev].
      split.
      -- right; exact Hin_rs.
      -- exact Hev.
Qed.




(* 
Lemma selectF_nil_all_false :
  forall (M : object_model) (SS : system_state M)
         (eval : env -> tm -> option val_b)
         (E : env) (var : string) (body : tm)
         (Th : T_h) (deps : list dep) (xs : list I_h),
    selectF M SS eval E var body Th deps xs = Some [] ->
    forall ih,
      In ih xs ->
      exists vb,
        eval (update E var (mk_var_b ih deps)) body = Some vb /\
        val_val vb = Ie_Single (Ih_Basic (Ib_Bool false)).
Proof.
  intros M SS eval E var body Th deps xs Hsel.
  induction xs as [|a tl IH]; intros ih Hin.
  - inversion Hin.
  - simpl in Hsel.
    (* 拆 eval (update ...) body *)
    destruct (eval (update E var (mk_var_b a deps)) body) as [vb|] eqn:Ha; try discriminate.
    (* 拆 vb 的值形状 *)
    destruct (val_val vb) as [v_single|Th' xs'] eqn:Hvv; try discriminate.
    (* v_single 必须是 Bool true/false 才可能继续 *)
    destruct v_single as [ihb|C0 o0]; try discriminate.
    destruct ihb as [b | z | r | s].
    -- (* ihb = Ib_Bool b *)
      destruct b.
      + (* b = true *)
        (* Hsel : option_map (a::) (selectF ... tl) = Some []  矛盾 *)
        simpl in Hsel. discriminate.
      + (* b = false *)
        (* Hsel : selectF ... tl = Some [] *)
        simpl in Hsel.
        (* 现在用 Hin 分析 ih 在 a::tl 里 *)
        simpl in Hin. destruct Hin as [-> | Hin_tl].
        * exists vb. split; [exact Ha|].
          (* 目标 val_val vb = ... false *)
          (* Hvv : val_val vb = Ie_Single (Ih_Basic (Ib_Bool false)) 在这个分支里应可由 Hvv 得到 *)
          (* 先把 Hvv 里的 ihb 替换掉： *)
          discriminate Hsel.
        * (* ih ∈ tl *)
          discriminate Hsel.
      + (* ihb = Ib_Int z *)
        simpl in Hsel. discriminate.
    -- (* ihb = Ib_Real r *)
      simpl in Hsel. discriminate.
    -- (* ihb = Ib_String s *)
      destruct r.
      --- (* r = true *)
        unfold option_map in Hsel.
        destruct (selectF M SS eval E var body Th deps tl) as [out_tl|] eqn:Htl;
        simpl in Hsel.
        ---- (* Hsel : Some (a :: out_tl) = Some [] *)
          discriminate Hsel.
        ---- (* Hsel : None = Some [] *)
          discriminate Hsel.
      --- (* r = false *)
        simpl in Hsel.
        simpl in Hin. destruct Hin as [Heq | Hin_tl].
        + subst ih.
          exists vb. split; [exact Ha|].
          (* 由 Hvv 得到 val_val vb = ... false *)
          exact Hvv.
        + (* ih ∈ tl *)
          eapply IH; eauto.
    -- (* ihb = Ih_Object (C0) o0 *)
      simpl in Hsel. discriminate. 
Qed. *)





Lemma project_rowsF_Forall2_eq
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex))
  (rows out : list RowData) :
  project_rowsF evalRex ps rows = Some out ->
  Forall2 (fun r r' => project_rowF evalRex ps r = Some r') rows out.
Proof.
  revert out.
  induction rows as [|r rs IH]; intros out H.
  - cbn in H. inversion H; subst. constructor.
  - cbn in H.
    destruct (project_rowF evalRex ps r) as [r'|] eqn:Hr; try discriminate.
    destruct (project_rowsF evalRex ps rs) as [out'|] eqn:Hrs; try discriminate.
    inversion H; subst.
    constructor; auto.
Qed.







Lemma project_rowsF_nil :
  forall evalRex ps rows,
    project_rowsF evalRex ps rows = Some [] ->
    rows = [].
Proof.
  intros evalRex ps rows.
  destruct rows as [|r rs]; simpl; intros H; auto.
  (* r::rs 情况下一般不可能返回 Some []，看定义：要么 discriminate，要么 inversion *)
  (* 通常： *)
  exfalso.
  (* 先把 project_rowF 和 project_rowsF 的结果拆出来 *)
  destruct (project_rowF evalRex ps r) as [r'|] eqn:Hr; simpl in H; try discriminate.
  destruct (project_rowsF evalRex ps rs) as [out|] eqn:Hrs; simpl in H; try discriminate.
Qed.


Lemma project_rowsF_on_nil :
  forall evalRex ps out,
    project_rowsF evalRex ps [] = Some out ->
    out = [].
Proof.
  intros. simpl in H. inversion H. reflexivity.
Qed.




Lemma lookup_row_cons_eq :
  forall cn v tl,
    lookup_row cn ((cn,v)::tl) = Some v.
Proof.
  intros cn v tl. simpl.
  destruct (String.string_dec cn cn) as [_|H]; [reflexivity|contradiction].
Qed.

Lemma lookup_row_singleton :
  forall cn v,
    lookup_row cn [(cn,v)] = Some v.
Proof.
  intros cn v. apply lookup_row_cons_eq.
Qed.




Lemma lookup_row_cons_neq :
  forall k cn v tl,
    k <> cn ->
    lookup_row cn ((k,v)::tl) = lookup_row cn tl.
Proof.
  intros k cn v tl Hneq. simpl.
  destruct (String.string_dec k cn) as [Heq|]; [contradiction|reflexivity].
Qed.



Lemma eval_proj_valsF_cons :
  forall evalRex r p tl vs,
    eval_proj_valsF evalRex r (p :: tl) = Some vs ->
    exists v vs',
      evalRex r (snd p) = Some v /\
      eval_proj_valsF evalRex r tl = Some vs' /\
      vs = v :: vs'.
Proof.
  intros evalRex r p tl vs H.
  simpl in H.
  destruct p as [cn e]; simpl in *.
  destruct (evalRex r e) as [v|] eqn:He; try discriminate.
  destruct (eval_proj_valsF evalRex r tl) as [vs'|] eqn:Htl; try discriminate.
  inversion H; subst vs.
  exists v, vs'. repeat split; auto.
Qed.



Lemma project_rowF_single :
  forall evalRex cn e r r',
    project_rowF evalRex [(cn,e)] r = Some r' ->
    exists v,
      evalRex r e = Some v /\ r' = [(cn, v)].
Proof.
  intros evalRex cn e r r' H.
  unfold project_rowF in H.
  simpl in H. (* map fst [(cn,e)] = [cn] *)
  destruct (nodup_stringb [cn]) eqn:Hnd; try discriminate.
  simpl in H. (* eval_proj_valsF on one element *)
  destruct (evalRex r e) as [v|] eqn:He; try discriminate.
  destruct (eval_proj_valsF evalRex r []) as [vs|] eqn:Hvs; try discriminate.
  (* eval_proj_valsF ... [] = Some [] *)
  simpl in Hvs. inversion Hvs; subst vs.
  inversion H; subst r'.
  exists v. split; auto.
Qed.



Lemma project_rowF_single_lookup :
  forall evalRex cn e r r' v,
    project_rowF evalRex [(cn,e)] r = Some r' ->
    evalRex r e = Some v ->
    lookup_row cn r' = Some v.
Proof.
  intros evalRex cn e r r' v Hpr He.
  pose proof (project_rowF_single evalRex cn e r r' Hpr) as [v' [He' ->]].
  rewrite He in He'. inversion He'. subst v'. apply lookup_row_singleton.
Qed.



Lemma class_row_has_oid :
  forall M SS SC DB C ts rows r,
    EncSchemaW M SC ->
    EncDBW M SS SC DB ->
    In C (CLASS M) ->
    lookup_table (sc_data SC) C = Some ts ->
    db_data SC DB C = Some rows ->
    In r rows ->
    exists o os,
      sigma_CLASS M SS C = Some os /\
      In o os /\
      lookup_row oid_col r = Some (Ira_Object C o).
Proof.
Admitted.



Lemma EncSchemaW_class_table_exists :
  forall (M : object_model) (SC : Schema) (c : class_name),
    EncSchemaW M SC ->
    In c (CLASS M) ->
    exists ts,
      lookup_table (sc_data SC) c = Some ts /\
      ClassTable_ok M c ts.
Proof.
  intros M SC c HEncSc Hin.
  unfold EncSchemaW, EncSchema in HEncSc.
  destruct HEncSc as [Hcls _].
  specialize (Hcls c Hin).
  exact Hcls.
Qed.



Lemma class_row_oid_from_EncDBW :
  forall (M : object_model) (SS : system_state M)
         (SC : Schema) (DB : DBInstance SC)
         (c : class_name) (rows : list RowData) (r : RowData),
    EncSchemaW M SC ->
    EncDBW M SS SC DB ->
    In c (CLASS M) ->
    db_data SC DB c = Some rows ->
    In r rows ->
    exists o os,
      sigma_CLASS M SS c = Some os /\
      In o os /\
      lookup_row oid_col r = Some (Ira_Object c o).
Proof.
  intros M SS SC DB c rows r HEncSc HEncDB HinC Hdb Hinr.

  (* 1) 由 EncSchemaW 得到类表 ts 存在 *)
  unfold EncSchemaW, EncSchema in HEncSc.
  destruct HEncSc as [Hcls _].
  specialize (Hcls c HinC).
  destruct Hcls as [ts [Htab _HClassOk]].

  (* 2) 用 EncDBW 的类表一致性拿到 ClassTableInst_ok *)
  unfold EncDBW, EncDB in HEncDB.
  destruct HEncDB as [Hdb_cls _Hdb_assoc].
  specialize (Hdb_cls c ts rows HinC Htab Hdb).
  unfold ClassTableInst_ok in Hdb_cls.
  destruct Hdb_cls as [_Hcover Hback].

  (* 3) 用“反向性”把任意行 r ∈ rows 回溯到某个对象 o ∈ sigma_CLASS *)
  specialize (Hback r Hinr).
  destruct Hback as [o [os [Hsig [Hino Hrowok]]]].

  (* 4) 从 ClassObjectRow_ok 里取出 oid 列性质 *)
  unfold ClassObjectRow_ok in Hrowok.
  destruct Hrowok as [Hoid _].

  exists o, os.
  repeat split; auto.
Qed.







Lemma project_rowsF_in :
  forall evalRex ps rows out r',
    project_rowsF evalRex ps rows = Some out ->
    In r' out ->
    exists r, In r rows /\ project_rowF evalRex ps r = Some r'.
Proof.
  intros evalRex ps rows.
  induction rows as [|r rs IH]; intros out r' Hproj Hin.
  - (* rows = [] *)
    simpl in Hproj. inversion Hproj; subst out.
    simpl in Hin. contradiction.
  - (* rows = r :: rs *)
    simpl in Hproj.
    destruct (project_rowF evalRex ps r) as [r1|] eqn:Hr; try discriminate.
    destruct (project_rowsF evalRex ps rs) as [out_rs|] eqn:Hrs; try discriminate.
    inversion Hproj; subst out.
    simpl in Hin. destruct Hin as [Hin_hd | Hin_tl].
    + (* r' = r1 *)
      subst r'. exists r. split; [left; reflexivity| exact Hr].
    + (* r' ∈ out_rs *)
      specialize (IH out_rs r' eq_refl Hin_tl) as [r0 [Hin0 Hrow0]].
      exists r0.
      split.
      -- right; exact Hin0.
      -- exact Hrow0.
Qed.



(* 把 I_h 编码成数据库里的 I_ra；非对象值不支持时返回 None *)
Definition enc_Ih (ih : I_h) : option I_ra :=
  match ih with
  | Ih_Object C o => Some (Ira_Object C o)
  | _ => None
  end.








Lemma lookup_row_some_in :
  forall cn r v,
    lookup_row cn r = Some v ->
    In (cn, v) r.
Proof.
  intros cn r; induction r as [| [k w] tl IH]; intros v H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (String.string_dec k cn) as [Heq|Hneq].
    + inversion H; subst. left. now subst.
    + right. apply IH. exact H.
Qed.


Lemma in_combine_nth_error :
  forall (ks : list string) (vs : list I_ra) k v,
    In (k, v) (combine ks vs) ->
    exists i,
      nth_error ks i = Some k /\
      nth_error vs i = Some v.
Proof.
  intros ks vs; revert vs.
  induction ks as [|k0 ks IH]; intros vs k v Hin.
  - simpl in Hin. contradiction.
  - destruct vs as [|v0 vs]; simpl in Hin.
    + contradiction.
    + simpl in Hin.
      destruct Hin as [Hin | Hin].
      * inversion Hin; subst.
        exists 0. simpl. auto.
      * specialize (IH vs k v Hin) as [i [Hk Hv]].
        exists (S i). simpl. auto.
Qed.




Lemma eval_proj_valsF_nth :
  forall evalRex r0 ps vs i cn e,
    eval_proj_valsF evalRex r0 ps = Some vs ->
    nth_error ps i = Some (cn, e) ->
    exists v,
      nth_error vs i = Some v /\
      evalRex r0 e = Some v.
Proof.
  intros evalRex r0 ps.
  induction ps as [| [cn0 e0] ps IH]; intros vs i cn e Heval Hnth.
  -  rewrite nth_error_nil in Hnth. discriminate Hnth.
  - simpl in Heval.
    destruct (evalRex r0 e0) as [v0|] eqn:He0; try discriminate.
    destruct (eval_proj_valsF evalRex r0 ps) as [vs'|] eqn:Htl; try discriminate.
    inversion Heval; subst vs; clear Heval.
    destruct i as [|i'].
    + simpl in Hnth. inversion Hnth; subst cn e.
      exists v0. simpl. auto.
    + simpl in Hnth.
    (* 用 IH 在 vs' 里找出对应 v *)
    destruct (IH vs' i' cn e eq_refl Hnth) as [v [Hvs Heval]].
    exists v.
    split.
    -- (* nth_error (v0::vs') (S i') = Some v *)
      simpl. exact Hvs.
    -- exact Heval.

Qed.






Lemma nth_error_map_fst_exists :
  forall (ps : list (string * rex)) i k,
    nth_error (map fst ps) i = Some k ->
    exists e, nth_error ps i = Some (k, e).
Proof.
  intros ps; induction ps as [| [k0 e0] tl IH]; intros i k H.
  - rewrite nth_error_nil in H. discriminate H.
  - destruct i as [|i'].
    + simpl in H. inversion H; subst k.
      exists e0. simpl. reflexivity.
    + simpl in H.
      specialize (IH i' k H) as [e He].
      exists e. simpl. exact He.
Qed.




Lemma existsb_eqb_true_iff :
  forall x xs,
    existsb (String.eqb x) xs = true <-> In x xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; simpl.
  - split; intro H; try discriminate; contradiction.
  - rewrite Bool.orb_true_iff.
    rewrite IH.
    split.
    + intro H. destruct H as [H|H].
      * left. apply String.eqb_eq in H. rewrite H. reflexivity.
      * right. exact H.
    + intro H. destruct H as [H|H].
      * left. apply String.eqb_eq. rewrite H. reflexivity.
      * right. exact H.
Qed.

Lemma nodup_stringb_sound :
  forall xs, nodup_stringb xs = true -> NoDup xs.
Proof.
  intro xs; induction xs as [|x tl IH]; simpl; intro H.
  - constructor.
  - apply Bool.andb_true_iff in H.
    destruct H as [Hnot Htl].
    apply Bool.negb_true_iff in Hnot.
    (* existsb ... tl = false *)
    assert (~ In x tl).
    { intro Hin.
      apply existsb_eqb_true_iff in Hin.
      (* Hin : existsb (String.eqb x) tl = true *)
      rewrite Hin in Hnot. discriminate.
    }
    constructor.
    + exact H.
    + apply IH. exact Htl.
Qed.




Lemma in_pair_same_fst_unique :
  forall (ps : list (string * rex)) k e1 e2,
    NoDup (map fst ps) ->
    In (k, e1) ps ->
    In (k, e2) ps ->
    e1 = e2.
Proof.
  intros ps; induction ps as [| [k0 e0] tl IH]; intros k e1 e2 Hnd Hin1 Hin2.
  - contradiction.
  - simpl in Hnd.
    inversion Hnd as [|k0' tl' Hnotin Hnd_tl]; subst k0' tl'.
    simpl in Hin1, Hin2.
    destruct Hin1 as [H1|H1]; destruct Hin2 as [H2|H2].
    + inversion H1; inversion H2; subst. reflexivity.
    + inversion H1; subst.
      (* (k,e0) in head, (k,e2) in tail *)
      exfalso.
      apply Hnotin. apply (in_map fst) in H2. exact H2.
    + inversion H2; subst.
      (* (k,e1) in tail, (k,e0) in head *)
      exfalso.
      apply Hnotin. apply (in_map fst) in H1. exact H1.
    + (* both in tail *)
      eapply IH; eauto.
Qed.





Lemma project_rowF_pullback_idcol :
  forall evalRex ps r0 r v,
    (forall row cn v, evalRex row (RCol cn) = Some v -> lookup_row cn row = Some v) ->
    In (val_col, RCol val_col) ps ->
    project_rowF evalRex ps r0 = Some r ->
    lookup_row val_col r = Some v ->
    lookup_row val_col r0 = Some v.
Proof.
  intros evalRex ps r0 r v Hcol Hid Hproj Hlook.
  unfold project_rowF in Hproj.
  destruct (nodup_stringb (map fst ps)) eqn:Hnodup; try discriminate.
  destruct (eval_proj_valsF evalRex r0 ps) as [vs|] eqn:Heval; try discriminate.
  inversion Hproj; subst r; clear Hproj.

  (* lookup_row -> In pair *)
  apply lookup_row_some_in in Hlook.
  (* In (val_col,v) (combine (map fst ps) vs) -> nth index *)
  eapply in_combine_nth_error in Hlook.
  destruct Hlook as [i [Hk Hv]].

  destruct (nth_error_map_fst_exists ps i val_col Hk) as [e Hnth_ps].

  destruct (eval_proj_valsF_nth evalRex r0 ps vs i val_col e Heval Hnth_ps)
    as [v' [Hv' He_e]].
  rewrite Hv in Hv'. inversion Hv'; subst v'; clear Hv'.

  pose proof (nodup_stringb_sound (map fst ps) Hnodup) as HNoDup.

  assert (In (val_col, e) ps) as Hin_ve.
  { eapply nth_error_In. exact Hnth_ps. }


  pose proof (in_pair_same_fst_unique ps val_col (RCol val_col) e HNoDup Hid Hin_ve) as Heq.
  subst e.

  apply (Hcol r0 val_col v).
  exact He_e.

Qed.





Lemma project_rowF_pullback_idcol_gen :
  forall evalRex ps r0 r cn v,
    (forall row cn v, evalRex row (RCol cn) = Some v -> lookup_row cn row = Some v) ->
    In (cn, RCol cn) ps ->
    project_rowF evalRex ps r0 = Some r ->
    lookup_row cn r = Some v ->
    lookup_row cn r0 = Some v.
Proof.
  intros evalRex ps r0 r cn v Hcol Hid Hproj Hlook.
  unfold project_rowF in Hproj.
  destruct (nodup_stringb (map fst ps)) eqn:Hnodup; try discriminate.
  destruct (eval_proj_valsF evalRex r0 ps) as [vs|] eqn:Heval; try discriminate.
  inversion Hproj; subst r; clear Hproj.

  apply lookup_row_some_in in Hlook.
  eapply in_combine_nth_error in Hlook.
  destruct Hlook as [i [Hk Hv]].

  destruct (nth_error_map_fst_exists ps i cn Hk) as [e Hnth_ps].

  destruct (eval_proj_valsF_nth evalRex r0 ps vs i cn e Heval Hnth_ps)
    as [v' [Hv' He_e]].
  rewrite Hv in Hv'. inversion Hv'; subst v'; clear Hv'.

  pose proof (nodup_stringb_sound (map fst ps) Hnodup) as HNoDup.

  assert (In (cn, e) ps) as Hin_ve.
  { eapply nth_error_In. exact Hnth_ps. }

  pose proof (in_pair_same_fst_unique ps cn (RCol cn) e HNoDup Hid Hin_ve) as Heq.
  subst e.

  apply (Hcol r0 cn v).
  exact He_e.
Qed.















Lemma project_rowsF_in_inv
  (evalRex : RowData -> rex -> option I_ra)
  (ps : list (ColName * rex))
  (rows0 rows1 : list RowData)
  (r : RowData)
  :
  project_rowsF evalRex ps rows0 = Some rows1 ->
  In r rows1 ->
  exists r0,
    In r0 rows0 /\
    project_rowF evalRex ps r0 = Some r.
Proof.
  revert rows1 r.
  induction rows0 as [|r0 rs IH]; intros rows1 r Hproj Hin.
  - simpl in Hproj. inversion Hproj; subst rows1. contradiction.
  - simpl in Hproj.
    destruct (project_rowF evalRex ps r0) as [r0'|] eqn:Hpr; try discriminate.
    destruct (project_rowsF evalRex ps rs) as [out|] eqn:Hrs; try discriminate.
    inversion Hproj; subst rows1; clear Hproj.
    simpl in Hin.
    destruct Hin as [Hr_eq | Hin_out].
    + subst r.
      exists r0. split.
      * left. reflexivity.
      * exact Hpr.
    + (* 这里用“first”兼容两种 IH 形状 *)
      destruct (IH out r) as [r00 [Hin00 Hpr00]].
      * first [ exact Hrs | exact eq_refl ].
      * exact Hin_out.
      * exists r00.
        split.
        -- right. exact Hin00.
        -- exact Hpr00.
Qed.









Lemma evalRexF_col :
  forall SC (DB : DBInstance SC) row cn v,
    evalRexF SC DB row (RCol cn) = Some v ->
    lookup_row cn row = Some v.
Proof.
  intros SC DB row cn v H.
  simpl in H. (* 这里会把 evalRexF 的 RCol 分支化简成 lookup_row *)
  exact H.
Qed.









Lemma cond_eq_true_lookup_valcol :
  forall SC (DB : DBInstance SC) (r : RowData),
    evalRexF SC DB r
      (RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)))
      = Some (Ira_Bool true) ->
    lookup_row val_col r = Some (Ira_Bool true).
Proof.
  intros SC DB r H.
  simpl in H.  (* 展开 evalRexF 的 RBinop *)
  (* 现在 H 是：
     match lookup_row val_col r, Some (Ira_Bool true) with
     | Some v1, Some v2 => binop_sem_ra (B_Comp BEq) v1 v2
     | _, _ => None
     end = Some (Ira_Bool true)
  *)
  destruct (lookup_row val_col r) as [v1|] eqn:Hlk; try discriminate.
  (* 化简 binop_sem_ra / comp_binop_sem_ra / lift_bool_Ie_ra *)
  simpl in H.
  (* binop_sem_ra -> comp_binop_sem_ra *)
  unfold binop_sem_ra in H; simpl in H.
  unfold comp_binop_sem_ra in H; simpl in H.
  unfold lift_bool_Ie_ra in H; simpl in H.
  (* comp_eq_sem_ra v1 (Ira_Bool true) 必须是 Some true *)
  unfold comp_eq_sem_ra in H.
  destruct v1; try discriminate.
  (* H : Some (Ira_Bool (Bool.eqb b true)) = Some (Ira_Bool true) *)
  destruct b; simpl in H; inversion H; reflexivity.
Qed.







(* 你的 cond *)
Definition cond_true : rex :=
  RBinop (B_Comp BEq) (RCol val_col) (RLit (Ira_Bool true)).

(* 选择 evalRex *)
Definition evalRex0 (SC : Schema) (DB : DBInstance SC) : RowData -> rex -> option I_ra :=
  fun r e => evalRexF SC DB r e.

(* A: RCol 分支就是 lookup_row，所以立刻能证 *)
Lemma evalRex0_col :
  forall SC (DB : DBInstance SC) (row : RowData) (cn : ColName) (v : I_ra),
    evalRex0 SC DB row (RCol cn) = Some v ->
    lookup_row cn row = Some v.
Proof. intros; cbn in H; exact H. Qed.



Lemma cond_true_lookup_valcol :
  forall SC (DB : DBInstance SC) (r : RowData),
    evalRexF SC DB r cond_true = Some (Ira_Bool true) ->
    lookup_row val_col r = Some (Ira_Bool true).
Proof.
  intros SC DB r H.
  unfold cond_true in H.
  cbn in H.
  (* evalRexF ... (RCol val_col) = lookup_row val_col r *)
  destruct (lookup_row val_col r) as [v|] eqn:Hlk; try discriminate.
  cbn in H.
  (* 右边 RLit true *)
  (* 现在是 binop_sem_ra (B_Comp BEq) v (Ira_Bool true) = Some (Ira_Bool true) *)
  unfold binop_sem_ra in H; cbn in H.
  unfold comp_binop_sem_ra in H; cbn in H.
  (* comp_eq_sem_ra v (Ira_Bool true) *)
  destruct v; try discriminate.
  (* v = Ira_Bool b *)
  cbn in H.
  (* lift_bool_Ie_ra (Some (Bool.eqb b true)) = Some (Ira_Bool true) *)
  unfold lift_bool_Ie_ra in H; cbn in H.
  inversion H; subst.
  destruct b; reflexivity.
Qed.






Lemma in_stringb_true_iff :
  forall (x : string) (xs : list string),
    in_stringb x xs = true <-> In x xs.
Proof.
  intros x xs.
  unfold in_stringb.
  induction xs as [|y ys IH]; simpl.
  - split; intro H; try discriminate; contradiction.
  - rewrite Bool.orb_true_iff.
    rewrite IH.
    split.
    + intro H. destruct H as [H|H].
      * left. apply String.eqb_eq in H. rewrite H. reflexivity.
      * right. exact H.
    + intro H. destruct H as [H|H].
      * left. apply String.eqb_eq. rewrite H. reflexivity.
      * right. exact H.
Qed.


Lemma in_proj_cols :
  forall vl x,
    In x vl ->
    In (x, RCol x) (proj_cols vl).
Proof.
  intros vl x Hin.
  unfold proj_cols.
  apply in_map_iff.
  exists x. split; auto.
Qed.




Lemma lookup_row_in_NoDup :
  forall cn v r,
    NoDup (map fst r) ->
    In (cn,v) r ->
    lookup_row cn r = Some v.
Proof.
  intros cn v r Hnd Hin.
  induction r as [|[k w] tl IH]; simpl in *.
  - contradiction.
  - inversion Hnd as [|k' tl' Hnotin Hnd']; subst.
    simpl in Hin. destruct Hin as [Hin|Hin].
    + inversion Hin; subst.
      destruct (String.string_dec cn cn); [reflexivity|contradiction].
    + destruct (String.string_dec k cn) as [Heq|Hneq].
      * subst cn.
        exfalso. apply Hnotin.
        apply in_map with (f:=fst) in Hin. exact Hin.
      * apply IH; auto.
Qed.











