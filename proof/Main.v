From Stdlib Require Import String ZArith Reals List.

From OCL Require Import Types Syntax Utils Typing Semantic.
Open Scope string_scope.



Definition model_has_type (Gamma : context) (M : obj_model) : Prop :=
  forall oid,
    let o := objects M oid in
    (* attributes *)
    (forall a,
        vhas_type M (attrs o a)
                  (Gamma (attr_key (cname o) a)))
    /\
    (* single-valued roles *)
    (forall r,
        vhas_type M (V_Object (roles o r))
                  (Gamma (role_key (cname o) r)))
    /\
    (* multi-valued roles *)
    (forall r,
        vhas_type M (V_Bag (map V_Object (nroles o r)))
                  (Gamma (nrole_key (cname o) r)))
    /\
    (* class membership consistency *)
    (forall C,
        In oid (cmap M C) ->
        cname o = C).



Definition env_has_type (Gamma : context) (M : obj_model) (E : env) : Prop :=
    forall x, 
        vhas_type M (E x) (Gamma x).


(* lookup（变量规则用） *)

Lemma env_has_type_lookup :
    forall Gamma M E x,
        env_has_type Gamma M E ->
        vhas_type M (E x) (Gamma x).
Proof.
    intros Gamma M E x H.
    unfold env_has_type in H.
    apply H.
Qed.


(* extend（绑定变量 / self / iterator 用） *)

Lemma env_has_type_extend :
  forall Gamma M E x v T,
    env_has_type Gamma M E ->
    vhas_type M v T ->
    env_has_type (t_update Gamma x T) M (t_update E x v).
Proof.
  intros Gamma M E x v T Henv Hv y.
  unfold env_has_type in *.
  destruct (String.eqb y x) eqn:Heq.
  - apply String.eqb_eq in Heq; subst.
    rewrite t_update_eq.
    rewrite t_update_eq.
    exact Hv.
  - apply String.eqb_neq in Heq.
    rewrite t_update_neq by congruence.
    rewrite t_update_neq by congruence.
    apply Henv.
Qed.


(* 不相关变量不受影响（可选，但常用） *)

Lemma env_has_type_update_other :
  forall Gamma M E x y v T,
    x <> y ->
    env_has_type Gamma M E ->
    vhas_type M ((t_update E x v) y) ((t_update Gamma x T) y).
Proof.
  intros Gamma M E x y v T Hneq Henv.
  unfold env_has_type in Henv.
  rewrite t_update_neq by congruence.
  rewrite t_update_neq by congruence.
  apply Henv.
Qed.




Lemma E_Select_in_left :
  forall M E var body xs ys v,
    E_Select M E var body xs ys ->
    In v ys ->
    In v xs.
Proof.
  intros M E var body xs ys v Hsel Hin.
  induction Hsel.
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst. simpl. left. reflexivity.
    + simpl. right. apply IHHsel. exact Hin'.
  - simpl. right. apply IHHsel. exact Hin.
Qed.



Lemma E_Reject_in_left :
  forall M E var body xs ys v,
    E_Reject M E var body xs ys ->
    In v ys ->
    In v xs.
Proof.
  intros M E var body xs ys v Hrej Hin.
  induction Hrej.
  - contradiction.
  - (* keep 分支：reject 里“保留/丢弃”的命名按你的构造子来 *)
    simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + subst. simpl. left. reflexivity.
    + simpl. right. apply IHHrej. exact Hin'.
  - (* drop 分支 *)
    simpl. right. apply IHHrej. exact Hin.
Qed.


Lemma E_Collect_in_attr :
  forall M E attr xs ys vout,
    E_Collect M E attr xs ys ->
    In vout ys ->
    exists vin, In vin xs /\ E_Attr M vin attr vout.
Proof.
  intros M E attr xs ys vout Hcol Hin.
  induction Hcol.
  - contradiction.
  - (* Cons *)
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst vout. exists v. split; [simpl; left; reflexivity | exact H ].
    + destruct (IHHcol Hin') as [vin [Hinxs Hat]].
      exists vin. split; [simpl; right; exact Hinxs | exact Hat ].
Qed.




Lemma E_RCollect_in_role :
  forall M E role xs ys vout,
    E_RCollect M E role xs ys ->
    In vout ys ->
    exists vin, In vin xs /\ E_Role M vin role vout.
Proof.
  intros M E role xs ys vout Hrc Hin.
  induction Hrc.
  - contradiction.
  - (* Cons *)
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst vout. exists v. split; [simpl; left; reflexivity | exact H ].
    + destruct (IHHrc Hin') as [vin [Hinxs Hrole]].
      exists vin. split; [simpl; right; exact Hinxs | exact Hrole ].
Qed.



Lemma E_NRCollect_in_left :
  forall M E nrole xs ys vout,
    E_NRCollect M E nrole xs ys ->
    In vout ys ->
    exists vin, In vin xs /\ exists oid,
      vin = V_Object oid /\
      In vout (map V_Object (nroles (objects M oid) nrole)).
Proof.
  intros M E nrole xs ys vout Hcollect.
  induction Hcollect as
    [ M E nrole
    | M E nrole oid xs ys Hrec IH ]; intros Hin.

  - (* nil *)
    simpl in Hin.
    contradiction.

  - (* cons *)
    simpl in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].

    + (* 在当前 Goal 下 *)
      inversion IH; subst.
      (* 现在通常会把 oid 和 ys 具体化成：
        oid = V_Object oid0
        ys  = map V_Object (nroles (objects M oid0) nrole)
      *)
      
      exists (V_Object oid0).
      split.
      * simpl. left. reflexivity.
      * exists oid0. split.
        -- reflexivity.
        -- (* Hin : In vout ys 现在变成 In vout (map ...) *)
          exact Hin.
    + (* Hin : In vout Hrec *)
      specialize (IHHcollect Hin) as [vin [Hinx [oid0 [Heq Hinmap]]]].

      exists vin.
      split.
      * (* In vin (oid :: xs) *)
        simpl. right. exact Hinx.
      * (* exists oid0, ... *)
        exists oid0. split; assumption.
Qed. 

          


Lemma vhas_type_bag_inv :
  forall M xs T,
    vhas_type M (V_Bag xs) (Ty_Bag T) ->
    Forall (fun v => vhas_type M v T) xs.
Proof.
  intros M xs T H.
  inversion H; subst.
  apply Forall_forall.
  exact H2.
Qed.




Lemma all_int_sound :
  forall xs zs,
    all_int xs = Some zs ->
    Forall (fun v => exists z, v = V_Int z) xs.
Proof.
  induction xs as [|v xs IH]; intros zs H.
  - (* xs = [] *)
    simpl in H.
    inversion H.
    constructor.
  - (* xs = v :: xs *)
    simpl in H.
    destruct v as [z | | | | | ]; try discriminate.
    (* 只剩 v = V_Int z *)
    destruct (all_int xs) as [zs'|] eqn:Hxs; try discriminate.
    inversion H; subst.
    constructor.
    + exists z. reflexivity.
    + apply (IH zs').
    reflexivity.
Qed.
      
Lemma vhas_type_int_inv :
  forall M v,
    vhas_type M v Ty_Int ->
    exists z, v = V_Int z.
Proof.
  intros M v H.
  inversion H; subst.
  eauto.
Qed.


Lemma all_int_complete :
  forall M xs,
    Forall (fun v => vhas_type M v Ty_Int) xs ->
    exists zs, all_int xs = Some zs.
Proof.
  intros M xs H.
  induction H as [|v xs Hv Hforall IH].
  - (* xs = [] *)
    exists nil.
    simpl. reflexivity.
  - (* xs = v :: xs *)
    destruct (vhas_type_int_inv M v Hv) as [z Hz].
    subst v.
    destruct IH as [zs Hzs].
    exists (z :: zs).
    simpl.
    rewrite Hzs.
    reflexivity.
Qed.






Lemma vhas_type_real_inv :
  forall M v,
    vhas_type M v Ty_Real ->
    exists r, v = V_Real r.
Proof.
  intros M v H.
  inversion H; subst.
  exists r. reflexivity.
Qed.





Lemma all_real_complete :
  forall M xs,
    Forall (fun v => vhas_type M v Ty_Real) xs ->
    exists rs, all_real xs = Some rs.

Proof.
  intros M xs H.
  induction H as [|v xs Hv Hforall IH].
  - (* xs = [] *)
    exists nil.
    simpl. reflexivity.
  - (* xs = v :: xs *)
    destruct (vhas_type_real_inv M v Hv) as [z Hz].
    subst v.
    destruct IH as [zs Hzs].
    exists (z :: zs).
    simpl.
    rewrite Hzs.
    reflexivity.
Qed.



Lemma all_int_none_of_all_real_cons :
  forall M v xs,
    vhas_type M v Ty_Real ->
    all_int (v :: xs) = None.
Proof.
  intros M v xs Hv.
  destruct (vhas_type_real_inv M v Hv) as [r ->].
  simpl.
  reflexivity.
Qed.




Hint Constructors vhas_type : core.
Hint Resolve env_has_type_lookup : core.
Hint Resolve env_has_type_extend : core.
Hint Resolve env_has_type_update_other : core.



Ltac solve_simple_con :=
  inversion Hty; subst; constructor.

Ltac solve_simple_eauto :=
  inversion Hty; subst; eauto.


Lemma object_class_sound :
  forall Gamma M E t oid cn,
    model_has_type Gamma M ->
    env_has_type Gamma M E ->
    has_type Gamma t (Ty_Object cn) ->
    cevalR M E t (V_Object oid) ->
    cname (objects M oid) = cn.
Proof.
  intros Gamma M E t oid cn Hmodel Henv Hty Hev.
  remember (V_Object oid) as v eqn:Hv.
  revert oid Hv cn Hty.
  (* 对求值证据做归纳 *)
  (* induction Hev. intros cn Hty; try inversion Hty; subst. *)
  induction Hev; try intros oid Hv cn Hty; try inversion Hv; subst; try inversion Hty; subst.
  - unfold env_has_type in Henv.
    specialize (Henv var).
    rewrite H0 in Henv.
    rewrite H2 in Henv.
    inversion Henv. reflexivity.
  - intros oid0 Hv cn Hty.
    (* 1) 从 Hv 得到 oid0 = oid *)
    inversion Hv; subst oid0.
    
    (* 2) 展开 env_has_type，并在 "self" 处特化 *)
    unfold env_has_type in Henv.
    specialize (Henv "self").
    
    (* 3) 用 H 和 H2 改写 Henv *)
    rewrite H in Henv.
    inversion Hty; subst.
    rewrite H2 in Henv.
    
    (* 4) 反演 vhas_type，得到类名一致性 *)
    inversion Henv. reflexivity.
  - intros oid0 Hv cn Hty.
    inversion Hty; subst.
    pose proof (IHHev Hmodel Henv oid eq_refl cn0 H2) as Hc0.
   (* 1) 先从 IHHev 得到 cname(objects M oid0) = cn0 *)
    unfold model_has_type in Hmodel.
    destruct (Hmodel oid) as [Hattrs _].
    specialize (Hattrs attr).
    rewrite Hc0 in Hattrs.
    rewrite H4 in Hattrs.
    rewrite Hv in Hattrs.

    (* 3. 得到结论 *)
    inversion Hattrs; subst. reflexivity.
  - intros oid0 Heq cn HtyRole.

    (* 1) 反演 typing：得到 cn0 以及 Gamma(role_key cn0 role)=Ty_Object cn *)
    inversion HtyRole; subst.
    (* 你需要的两个东西：
      H3 : has_type Gamma t (Ty_Object cn0)
      H4 : Gamma (role_key cn0 role) = Ty_Object cn
    *)
    
    (* 2) 用 IHHev 得到基对象 oid 的类名 *)
    pose proof (IHHev Hmodel Henv oid eq_refl cn0 H3) as Hc_base.
    (* Hc_base : cname (objects M oid) = cn_base *)
    
    (* 3) 从模型良构性拿到 role 的值类型正确性 *)
    destruct (Hmodel oid) as [_ [Hroles _]].
    specialize (Hroles role).
    (* Hroles :
      vhas_type M (V_Object (roles (objects M oid) role))
                (Gamma (role_key (cname (objects M oid)) role)) *)
    
    (* 4) 把 cname(objects M oid) 改写成 cn_base，再把 Gamma(role_key ..) 改成 Ty_Object cn *)
    rewrite Hc_base in Hroles.
    rewrite H4 in Hroles.
    
    (* 5) 把等式 Heq 用来改写 value *)
    rewrite Heq in Hroles.
    (* 现在 Hroles : vhas_type M (V_Object oid0) (Ty_Object cn) *)
    
    (* 6) 反演 vhas_type，得到类名一致性 *)
    inversion Hroles; subst. reflexivity.
  - intros oid0 Heq.
    discriminate Heq.
Qed.





Theorem preservation_bigstep :
    forall Gamma M E t v T,
      model_has_type Gamma M ->
      env_has_type Gamma M E ->
      has_type Gamma t T ->
      cevalR M E t v ->
      vhas_type M v T.
  (* with preservation_bagliteral :
    forall Gamma M E ts vs T,
      env_has_type Gamma M E ->
      (forall t, In t ts -> has_type Gamma t T) ->
      E_BagLiteral M E ts vs ->
      forall v, In v vs -> vhas_type M v T. *)
  Proof.
    (* - preservation_bigstep *)
      intros Gamma M E t v T Hmodel Henv Hty Hev.
      revert T Hty.
      induction Hev; intros T0 Hty; try solve_simple_con.
      + intros v HIn. inversion HIn.
      + intros v Hin.
        revert v Hin.
        induction H; try intros v Hin.
        * (* E_BagLiteral_nil: ts = [], vs = [] *)
          inversion Hin.

        * intros v0 Hin.
          simpl in Hin.
          destruct Hin as [Hv0 | Hin0].
          -- (* v0 = v *)
            subst v0.
            (* 从 H2 取 t : T *)
            assert ( has_type Gamma t T0) as HtTy.
            { apply H2. left. reflexivity. }
            inversion H; subst.
          
          - (* v0 ∈ vl *)
            (* 先从 Hty 拆出尾部 CBagLiteral tl 的类型 *)
            inversion Hty; subst.
            (* inversion 后通常会产生一个形如：
                Hty_tl : has_type Gamma (CBagLiteral tl) (Ty_Bag T)
              的假设；名字按你实际生成的为准。
            *)
          
            (* 构造尾部逐项类型假设 *)
            have H2_tl : forall t0 : tm, In t0 tl -> has_type Gamma t0 T.
            { intros t0 Hin_t0. apply H2. right. exact Hin_t0. }
          
            (* 用 IHE_BagLiteral 解决 *)
            eapply IHE_BagLiteral; eauto.
          

        

      
      eapply preservation_bagliteral; eauto.
      + inversion Hty; subst. eapply IHHev; eauto.
        eapply T_ForAll with (T := Ty_Object C).
        * (* 证明 allInstances 的类型 *)
          apply T_AllInstances.
        * (* 证明 body 在 self 绑定后是 Bool *)
          exact H3.
      + inversion Hty; subst.
      (* 现在你会得到：Gamma var = T 或者直接 T = Gamma var 之类的等式 *)
        eapply env_has_type_lookup; eauto.
      + inversion Hty; subst. rewrite <- H. rewrite <- H0.
        eapply env_has_type_lookup; eauto.
      + inversion Hty; subst.
        pose proof (Hmodel oid) as Hm. 
        destruct Hm as [Hattrs _].
        specialize (Hattrs attr).
        assert (cname (objects M oid) = cn) as Hcn.
        { (* 用 t 的静态类型 + 求值结果，推出对象真实类名 = cn *)
          (* 这一步需要一个桥梁引理；下面给出它的形状 *)
          eapply object_class_sound; eauto.
          (* 这里的 eauto 会用 Hmodel Henv H3 Hev *)
        }
        rewrite Hcn in Hattrs. apply Hattrs.
      +  (* 1) 从 Hty 反演出 t 的对象类型 cn0，以及 role_key 对应的类型 = T *)
        inversion Hty; subst.
        (* inversion Hty as [ (* ... *) cn0 Ht_base Hkey ]; subst. *)
        
        (* 2) 用 object_class_sound（或你前面已经证明的引理）得到 cname(objects M oid)=cn0 *)
        pose proof (object_class_sound Gamma M E t oid cn Hmodel Henv H3 Hev) as Hc0.
        (* Hc0 : cname (objects M oid) = cn0 *)
        
        (* 3) 从 Hmodel 取出 role 的 vhas_type 信息 *)
        destruct (Hmodel oid) as [_ [Hroles _]].
        specialize (Hroles role).
        (* Hroles :
          vhas_type M (V_Object (roles (objects M oid) role))
                    (Gamma (role_key (cname (objects M oid)) role)) *)
        
        (* 4) 用 Hc0 把 cname(objects M oid) 改成 cn0 *)
        rewrite Hc0 in Hroles.
        
        (* 5) 用 Hkey 把 Gamma(role_key cn0 role) 改成 T *)
        rewrite H5 in Hroles. assumption.
      + intros v Hv.
        (* 1. 从模型良构性中取出 nrole 的 vhas_type *)
        destruct (Hmodel oid) as [_ [_ [Hnroles _]]].
        specialize (Hnroles nrole).
        (* Hnroles :
          vhas_type M
            (V_Bag (map V_Object (nroles (objects M oid) nrole)))
            (Gamma (nrole_key (cname (objects M oid)) nrole)) *)
        
        (* 2. 用 object_class_sound 得到基对象类名 *)
        pose proof
          (object_class_sound Gamma M E t oid cn
            Hmodel Henv H3 Hev) as Hc0.
        (* Hc0 : cname (objects M oid) = cn *)
        
        rewrite Hc0 in Hnroles. rewrite H5 in Hnroles.
        (* 现在：
          Hnroles :
            vhas_type M
              (V_Bag (map V_Object (nroles (objects M oid) nrole)))
              (Ty_Bag (Ty_Object T0)) *)
        
        (* 3. 反演 vhas_type 的 Bag 分支 *)
        (* inversion Hnroles as [| | | ? ? ? Hforall]; subst. *)
        inversion Hnroles; subst.
        
        (* 4. 用 Bag 的逐元素性质 *)
        apply H1. assumption.
      + intros v Hv.
        (* 把 In v (map V_Object ...) 拆成存在一个 oid *)
        apply in_map_iff in Hv.
        destruct Hv as [oid0 [Hv_eq Hin]].
        subst v.
        
        (* 从 model_has_type 取出 “class membership consistency” 分量 *)
        destruct (Hmodel oid0) as [_ [_ [_ Hcmap]]].
        specialize (Hcmap C Hin).
        (* Hcmap : cname (objects M oid0) = C *)
        
        (* 用 vhas_type 的对象构造子收口 *)
        rewrite <- Hcmap. constructor.
      + (* 反演 typing：CBoolUn 的 typing 规则应当强制 T = Ty_Bool，并给出 t : Ty_Bool *)
        inversion Hty; subst.
        (* 反演后你应该得到类似：
          Ht : has_type Gamma t Ty_Bool
          并且 T 被 subst 成 Ty_Bool
        *)
        
        (* 用 IH 得到 v : Bool *)
        assert (vhas_type M v Ty_Bool) as Hvty.
        { eapply IHHev; eauto. }
        (* 如果你没有 have，用 pose proof/assert： *)
        (* pose proof (IHHev Hmodel Henv Ht) as Hvty. *)
        
        (* 从 vhas_type 推出 v 的形状必须是 V_Bool b *)
        inversion Hvty; subst.
        (* 得到 v = V_Bool b *)
        
        (* 展开 bool_unop_sem，根据 op 和 v = V_Bool b 推出 v' = V_Bool ... *)
        (* 通常：bool_unop_sem UNot (V_Bool b) = Some (V_Bool (negb b)) *)
        simpl in H.
        inversion H; subst.
        destruct op; simpl in H1. inversion H1; subst. constructor.
      + inversion Hty; subst.
        * (* 1) 子项 preservation：得到 v 是 Int *)
          pose proof (IHHev Hmodel Henv Ty_Int H5) as Hvty.
          inversion Hvty; subst.   (* 现在 v = V_Int z0 之类 *)
          
          (* 2) 用 op 是 UNeg 或 UAbs 分情况 *)
          destruct H3 as [Hop | Hop]; subst op; simpl in H;
          inversion H; subst; constructor.

        * (* 1) 子项 preservation：得到 v 是 Real *)
          pose proof (IHHev Hmodel Henv Ty_Real H5) as Hvty.
          inversion Hvty; subst.   (* 现在 v = V_Real r0 *)
          destruct H3 as [Hop | Hop]; subst op; simpl in H;
          inversion H; subst; constructor.

        * (* 1) 子项 preservation：v 的类型是 Real *)
          pose proof (IHHev Hmodel Henv Ty_Real H5) as Hvty.
          inversion Hvty; subst.   (* 现在 v = V_Real r *)

          (* 2) op 分情况：UFloor / URound *)
          destruct H3 as [Hop | Hop]; subst op; simpl in H.
          -- (* UFloor *)
            inversion H; subst.
          -- (* URound *)
            inversion H; subst.
        
      +  (* 1) 由 typing 反演：UFloor 的输入/输出类型 *)
        inversion Hty; subst; try constructor.
        (* 现在应当得到：
          Ht : has_type Gamma t Ty_Real
          并且 T 被替换为 Ty_Int
        *)
        destruct H3 as [Hop | Hop]; discriminate.
      + inversion Hty; subst; try constructor.
        destruct H3 as [Hop | Hop]; discriminate.
      + inversion Hty; subst.

        (* 由子项类型推出 v 的类型 *)
        pose proof (IHHev Hmodel Henv _ H4) as Hvty.
        (* 注意：H4 是 inversion Hty 后得到的 “has_type Gamma t ...” 那条，名字可能不同 *)
        
        inversion Hvty; subst.
        
        (* 展开语义，反演 Some v'，构造 vhas_type *)
        destruct op; simpl in H; inversion H; subst; constructor.
      +  inversion Hty; subst.
        (* 你会得到两条子项 typing：Ht1 : has_type Gamma t1 T1, Ht2 : has_type Gamma t2 T2 *)
        
        pose proof (IHHev1 Hmodel Henv _ H6) as Hv1.
        pose proof (IHHev2 Hmodel Henv _ H7) as Hv2.
        
        (* 反演得到 v1/v2 的具体构造 *)
        inversion Hv1; subst;
        inversion Hv2; subst.
        * destruct H4 as [Hop | [Hop | Hop]]; subst op; simpl in H;
          inversion H; subst; constructor.
        * (* 1) 子项 preservation：v1、v2 都是 Int *)
          pose proof (IHHev1 Hmodel Henv Ty_Int H5) as Hv1.
          pose proof (IHHev2 Hmodel Henv Ty_Int H6) as Hv2.
          
          (* 2) 反演得到 v1 = V_Int n1, v2 = V_Int n2 *)
          inversion Hv1; subst.
          inversion Hv2; subst.
          
          (* 3) 展开除法语义并反演 Some *)
          simpl in H.
          destruct (n0 =? 0)%Z eqn:Hz; try discriminate.
          inversion H; subst.
          constructor.
        * pose proof (IHHev1 Hmodel Henv Ty_Real H5) as Hv1.
          pose proof (IHHev2 Hmodel Henv Ty_Real H6) as Hv2.
          inversion Hv1; subst.
          inversion Hv2; subst.
          destruct op; simpl in H; try discriminate; inversion H; subst; try constructor.
          destruct (Reqb r0 0) eqn:Hz; try discriminate.
          inversion H1; subst.
          constructor.
      + inversion Hty; subst.
        (* 你会得到两条子项类型：Ht1 : has_type Gamma t1 T1, Ht2 : has_type Gamma t2 T2 *)
        
        pose proof (IHHev1 Hmodel Henv _ H5) as Hv1.
        pose proof (IHHev2 Hmodel Henv _ H6) as Hv2.
        
        inversion Hv1; subst.
        inversion Hv2; subst.
        
        destruct op; simpl in H; try discriminate; inversion H; subst; constructor.
      + inversion Hty; subst.
        (* 这里会出现 Ht1 : has_type Gamma t1 T1, Ht2 : has_type Gamma t2 T2 ——名字按实际替换 *)
        
        pose proof (IHHev1 Hmodel Henv _ H5) as Hv1.
        pose proof (IHHev2 Hmodel Henv _ H6) as Hv2.
        inversion Hv1; subst.
        inversion Hv2; subst.
        
        destruct op; simpl in H; try discriminate; inversion H; subst; try constructor.
        * destruct (n0 =? 0)%Z eqn:Hz; try discriminate.
          inversion H1; subst.
          constructor.
        * destruct (n0 =? 0)%Z eqn:Hz; try discriminate.
          inversion H1; subst.
          constructor.
        * pose proof (IHHev1 Hmodel Henv Ty_Real H5) as Hv1.
          pose proof (IHHev2 Hmodel Henv Ty_Real H6) as Hv2.
          inversion Hv1; subst.
          inversion Hv2; subst.
          destruct op; simpl in H; try discriminate; inversion H; subst; constructor.
      + pose proof (IHHev1 Hmodel Henv (Ty_Bag T) H2) as Hvxs.
        pose proof (IHHev2 Hmodel Henv (Ty_Bag T) H4) as Hvys.
        
        inversion Hvxs; subst.
        inversion Hvys; subst.
        (* 这里假设 vhas_type 对 Bag 的构造子形如：
            VHT_Bag : (forall v, In v xs -> vhas_type M v T) -> vhas_type M (V_Bag xs) (Ty_Bag T)
          所以反演后得到 Hxs / Hys 这类“元素类型保持”前提。
        *)
        
        intros v Hin.
        unfold bag_union in Hin.                (* 如果 bag_union 定义为 xs ++ ys *)
        apply in_app_iff in Hin.
        destruct Hin as [Hin | Hin].
        * apply H1; assumption.
        * apply H3; assumption.
      + pose proof (IHHev1 Hmodel Henv (Ty_Bag T) H2) as Hvxs.
        pose proof (IHHev2 Hmodel Henv (Ty_Bag T) H4) as Hvys.
        inversion Hvxs; subst.
        inversion Hvys; subst.
        (* 现在上下文里应有 Hxs : forall v, In v xs -> vhas_type M v T *)
        
        intros v Hin.
        unfold bag_intersect in Hin.
        apply filter_In in Hin.
        destruct Hin as [Hin_xs _].
        apply H1; assumption.
      + pose proof (IHHev1 Hmodel Henv (Ty_Bag T) H2) as Hvxs.
        inversion Hvxs; subst.
        
        intros v Hin.
        unfold bag_difference in Hin.
        apply filter_In in Hin.
        destruct Hin as [Hin_xs _].
        apply H1; assumption.
      + (* 1) 从两个 IH 得到 xs / ys 的元素类型保持 *)
        pose proof (IHHev1 Hmodel Henv (Ty_Bag T) H2) as Hvxs.
        pose proof (IHHev2 Hmodel Henv (Ty_Bag T) H4) as Hvys.
        inversion Hvxs; subst.
        inversion Hvys; subst.
        (* 现在上下文中应当有：
          Hxs : forall v, In v xs -> vhas_type M v T
          Hys : forall v, In v ys -> vhas_type M v T
        *)

        (* 2) 进入目标 *)
        intros v Hin.
        unfold bag_symdiff in Hin.

        (* 3) 如果 bag_symdiff 是 (bag_difference xs ys) ++ (bag_difference ys xs) 这种 union/++ 形式 *)
        apply in_app_iff in Hin.
        destruct Hin as [Hin | Hin].
        * (* v 来自 xs \ ys *)
          (* 这里用“difference 的元素来自左边” *)
          apply H1.
          (* 如果你 bag_difference 定义为 filter ... xs，可用 filter_In *)
          unfold bag_difference in Hin.
          apply filter_In in Hin.
          destruct Hin as [Hin_left _].
          exact Hin_left.
        * (* v 来自 ys \ xs *)
          apply H3.
          unfold bag_difference in Hin.
          apply filter_In in Hin.
          destruct Hin as [Hin_left _].
          exact Hin_left.
      + intros v Hin.
        (* 先把上面 inversion 得到的“vs 元素类型保持”假设命名为 Hvs *)
        (* 例如：rename H0 into Hvs.  具体名字按你上下文里出现的改 *)
        
        revert v Hin.
        induction H; intros v0 Hin.
        * (* E_Select ... [] [] *)
          contradiction.
        
        * (* E_Select_keep: 选中头部 x，输出 (x :: vs') *)
          simpl in Hin.
          destruct Hin as [Hv | Hin'].
          -- subst v.
            pose proof (IHHev Hmodel Henv (Ty_Bag T) H5) as Hvbag.
            inversion Hvbag; subst.
            (* 现在上下文里会出现类似：Hvs : forall v, In v (v0 :: tl) -> vhas_type M v T *)
            apply H3. simpl. left. reflexivity.

          -- (* 1) 先用 IHHev 得到输入 bag 的值类型 *)
            pose proof (IHHev Hmodel Henv (Ty_Bag T) H5) as Hvbag.
            
            (* 2) 反演 bag 的值类型，得到“输入列表每个元素都是 T” *)
            inversion Hvbag; subst.
            (* 现在上下文里会出现类似：
              Hvs : forall x : value, In x (v :: tl) -> vhas_type M x T
              （名字可能不是 Hvs，按实际改）
            *)
            
            (* 3) 由 E_Select_in_left 得到 v0 ∈ tl *)
            assert (Hin_tl : In v0 tl).
            { eapply E_Select_in_left; eauto. }
            
            (* 4) 提升到 In v0 (v :: tl)，再用 Hvs 收口 *)
            apply H3.
            simpl. right. exact Hin_tl.
        * pose proof (IHHev Hmodel Henv (Ty_Bag T) H5) as Hvbag.
          inversion Hvbag; subst.
          (* 得到 Hvs : forall x, In x (v :: tl) -> vhas_type M x T  （名字按实际改） *)
          
          assert (Hin_tl : In v0 tl).
          { eapply E_Select_in_left; eauto. }
          
          apply H3.
          simpl. right. exact Hin_tl.
      + (* 1) 从 IHHev 得到输入 bag 的元素类型保持 *)
        pose proof (IHHev Hmodel Henv (Ty_Bag T) H5) as Hvbag.
        inversion Hvbag; subst.
        (* 得到 Hvs : forall x, In x vs -> vhas_type M x T  （名字按实际改） *)

        (* 2) 证明输出元素类型 *)
        intros v Hin.
        apply H2.

        (* 3) 把 In v vs' 推回 In v vs *)
        eapply E_Reject_in_left; eauto.
      + pose proof (IHHev Hmodel Henv (Ty_Bag (Ty_Object cn)) H3) as Hvbag.
        inversion Hvbag; subst.
        (* 得到：Hvs : forall x, In x vs -> vhas_type M x (Ty_Object cn) *)
        (* 目标：forall v, In v vs' -> vhas_type M v (Gamma (attr_key cn attr)) *)
        intros v Hin.
        revert v Hin.
        induction H.
        * (* E_CollectNil *)
          intros v Hin. contradiction.

        * (* E_CollectCons... 假设这一支会生成一个 head_out 并递归 *)
          intros v0 Hin.
          simpl in Hin.
          destruct Hin as [Heq | Hin'].
          -- subst v0.
            (* 1) v 在输入 (v :: tl) 里，因此 v : Ty_Object cn *)
            assert (vhas_type M v (Ty_Object cn)) as  Hv_ty.
            { apply H2. simpl. left. reflexivity. }

            (* 2) 反演 Hv_ty，得到 v = V_Object oid 以及 cname(objects M oid)=cn *)
            inversion Hv_ty; subst v.
            (* 上面这一行的 as-pattern 需要按你的 vhas_type 构造子调整：
              关键是要得到：
              - v = V_Object oid0 （通过 subst）
              - Hcname : cname (objects M oid0) = cn
            *)

            (* 3) 从 model_has_type 取出该对象 oid0 的属性类型事实 *)
            specialize (Hmodel oid) as [Hattrs _].
            specialize (Hattrs attr).
            (* 现在：
              Hattrs :
                vhas_type M (attrs (objects M oid0) attr)
                          (Gamma (attr_key (cname (objects M oid0)) attr))
            *)

            (* 4) 用 cname=cn 改写类型索引 *)
            rewrite H5 in Hattrs.
            (* 现在：
              Hattrs :
                vhas_type M (attrs (objects M oid0) attr)
                          (Gamma (attr_key cn attr))
            *)

            (* 5) 用 E_Attr 连接 v_attr 和 attrs(...)attr *)
            inversion H; subst.
            (* 理想情况下，此时会得到类似：
              v_attr = attrs (objects M oid0) attr
              或者 attrs (objects M oid0) attr = v_attr
            *)
            (* 若得到的是 attrs(...) = v_attr： rewrite <- Heq in Hattrs.
              若得到的是 v_attr = attrs(...): rewrite Heq in Hattrs.
            *)

            (* 6) 收口 *)
            exact Hattrs.
          -- (* 1) 从结构引理得到：v0 来自 tl 中某个 vin 的属性 *)
            destruct (E_Collect_in_attr M E attr tl out_tl v0 H0 Hin') as [vin [Hin_tl Hat]].
            
            (* 2) vin ∈ tl => vin : Ty_Object cn *)
            assert ( vhas_type M vin (Ty_Object cn)) as  Hvin_ty.
            { apply H2. simpl. right. exact Hin_tl. }
            
            (* 3) 用 Hvin_ty + Hmodel + Hat (E_Attr) 证明 v0 的类型 *)
            (* 下面这段和你前一个“头部 v_attr”的证明完全同型，只是把 v 换成 vin，把 v_attr 换成 v0 *)
            
            inversion Hvin_ty; subst.
            specialize (Hmodel oid) as [Hattrs _].  (* oid0 是 inversion 得到的对象 id *)
            specialize (Hattrs attr).
            inversion Hat; subst.                   (* 把 v0 对齐为 attrs(objects M oid0) attr *)
            exact Hattrs.
      + intros vout Hin.

        (* 2.1 从结构引理得到：vout 来自某个输入 vin 的 role *)
        destruct (E_RCollect_in_role M E role vs vs' vout H Hin)
          as [vin [Hin_vs Hrole]].
        
        (* 2.2 用 IHHev + H3 得到输入元素类型：vin : Ty_Object cn *)
        pose proof (IHHev Hmodel Henv (Ty_Bag (Ty_Object cn)) H3) as Hvbag.
        inversion Hvbag; subst.
        (* 得到 Hvs : forall x, In x vs -> vhas_type M x (Ty_Object cn) *)
        
        assert (vhas_type M vin (Ty_Object cn)) as Hvin_ty.
        { apply H2. exact Hin_vs. }
        
        (* 2.3 反演 Hvin_ty：vin = V_Object oid 且 cname(objects M oid)=cn *)
        inversion Hvin_ty; subst.
        
        (* 2.4 用 Hmodel oid 取出 role 的良型信息 *)
        specialize (Hmodel oid) as [_ [Hroles _]].  (* 注意：取第二个合取：single-valued roles *)
        specialize (Hroles role).
        (* Hroles : vhas_type M (V_Object (roles (objects M oid) role))
                            (Gamma (role_key (cname (objects M oid)) role)) *)
        rewrite H5 in Hroles.         (* Gamma(role_key cn role)=Ty_Object C *)
        
        (* 2.6 用 Hrole 把 vout 对齐为 V_Object (roles ...) 或者等式对应 rewrite *)
        inversion Hrole; subst.       (* 或者 rewrite Hrole in Hroles / rewrite <-Hrole in Hroles *)
        
        exact Hroles.
      +  intros vout Hin.

        (* 1) 追溯 vout 来自哪个输入对象 oid 的 nrole 列表 *)
        destruct (E_NRCollect_in_left M E nrole vs vs' vout H Hin)
          as [vin [Hin_vs [oid [Heqvin Hin_inmap]]]].
        subst vin.
        
        (* 2) 由 IHHev + H3 得到输入元素类型：vs 每个元素都是 Ty_Object cn *)
        pose proof (IHHev Hmodel Henv (Ty_Bag (Ty_Object cn)) H3) as Hvbag.
        inversion Hvbag; subst.
        (* 得到 Hvs : forall x, In x vs -> vhas_type M x (Ty_Object cn) *)
        
        assert ( vhas_type M (V_Object oid) (Ty_Object cn)) as Hvin_ty.
        { apply H2. exact Hin_vs. }
        
        (* 3) 反演 Hvin_ty，拿到 cname(objects M oid)=cn *)
        inversion Hvin_ty; subst.  (* 按你 vhas_type 构造子调整 *)
        
        (* 4) 用 Hmodel 得到该对象的 nrole bag 类型 *)
        specialize (Hmodel oid) as [_ [_ [Hnroles _]]].  (* 取 model_has_type 的第三块：multi-valued roles *)
        specialize (Hnroles nrole).
        (* Hnroles :
          vhas_type M (V_Bag (map V_Object (nroles (objects M oid) nrole)))
                    (Gamma (nrole_key (cname (objects M oid)) nrole))
        *)
        
        (* 5) 用 cname=cn、再用 H5 改写成 Ty_Bag (Ty_Object C) *)
        (* rewrite Hcname in Hnroles. *)
        rewrite H5 in Hnroles.
        (* 现在 Hnroles :
          vhas_type M (V_Bag (map V_Object (nroles ... nrole))) (Ty_Bag (Ty_Object C))
        *)
        
        (* 6) 反演 vhas_type 的 Bag 分支，得到 bag 元素都具有 Ty_Object C *)
        inversion Hnroles; subst.
        (* 得到类似：
          Hall : forall v, In v (map V_Object (nroles ...)) -> vhas_type M v (Ty_Object C)
        *)
        
        (* 7) 应用 Hall 到 Hin_inmap *)
        apply H4.
        exact Hin_inmap.
      + (* 1) 反演 typing，拿到 t 的 bag 类型以及结果类型关系 *)
        inversion Hty; subst.
        * unfold aggop_sem in H.
          simpl in H.
          inversion H; subst.
          (* 现在 v 被替换成 V_Int (Z.of_nat (length xs)) *)
          
          constructor.
          (* 或者：apply vhas_type_int. 取决于你 vhas_type 的构造子名字 *)
        * destruct H3 as [Hopmin | [Hopmax | Hopsum]]; subst op;
          unfold aggop_sem in H; simpl in H.
          --pose proof (IHHev Hmodel Henv (Ty_Bag Ty_Int) H5) as HbagTy.
            pose proof (vhas_type_bag_inv M xs Ty_Int HbagTy) as Hall.
            
            destruct (all_int_complete M xs Hall) as [zs Hzs].
            rewrite Hzs in H.
            destruct zs as [|z zs']; simpl in H; try discriminate.
            inversion H; subst.
            constructor.
          -- (* AggMax case *)

            (* 1) bag 的值类型 *)
            pose proof (IHHev Hmodel Henv (Ty_Bag Ty_Int) H5) as HbagTy.
            
            (* 2) 展开 bag typing -> Forall *)
            pose proof (vhas_type_bag_inv M xs Ty_Int HbagTy) as Hall.
            
            (* 3) 由 Forall Int 推出 all_int xs = Some zs *)
            destruct (all_int_complete M xs Hall) as [zs Hzs].
            
            (* 4) 把 Hzs 写进 H，消掉 all_int 的 match *)
            rewrite Hzs in H.
            
            (* 5) zs 为空会落到 Some nil => None，与 Some v 矛盾；非空则得到 V_Int ... *)
            destruct zs as [| z zs']; simpl in H.
            ++ discriminate.
            ++ inversion H; subst.
              constructor.
          -- (* AggSum case *)

            (* 1) bag 的值类型 *)
            pose proof (IHHev Hmodel Henv (Ty_Bag Ty_Int) H5) as HbagTy.
            
            (* 2) 展开 bag typing -> Forall *)
            pose proof (vhas_type_bag_inv M xs Ty_Int HbagTy) as Hall.
            
            (* 3) 由 Forall Int 推出 all_int xs = Some zs *)
            destruct (all_int_complete M xs Hall) as [zs Hzs].
            
            (* 4) rewrite 到 H 中，消去 match *)
            rewrite Hzs in H.
            simpl in H.
            
            (* 5) 反演得到 v 的具体形状，然后用 Int 的 vhas_type 构造子 *)
            inversion H; subst.
            destruct zs as [|z zs'].
            ++ (* zs = [] *)
              discriminate H1.
            ++ (* zs = z :: zs' *)
              inversion H1; subst.
              constructor.
        * (* 1) 先得到 bag 值的类型：V_Bag xs : Ty_Bag Ty_Real *)
          pose proof (IHHev Hmodel Henv (Ty_Bag Ty_Real) H5) as HbagTy.
          
          (* 2) 反推出 xs 中每个元素都是 Ty_Real *)
          pose proof (vhas_type_bag_inv M xs Ty_Real HbagTy) as HallReal.
          
          (* 3) all_real 必定成功 *)
          destruct (all_real_complete M xs HallReal) as [rs Hrs].
          
          (* 4) 对 op 分类讨论 *)
          destruct H3 as [Hopmin | [Hopmax | Hopsum]]; subst op.
          
          -- (* ================= AggMin : Ty_Real ================= *)
            (* 先把 xs 分成空/非空，保证能用 all_int_none_of_all_real_cons *)
            destruct xs as [|v0 xs'].
            ++ (* xs = [] *)
              (* 此时 all_real [] = Some []，AggMin 的语义会返回 None，与 Some v 矛盾 *)
              unfold aggop_sem in H; simpl in H.
              (* all_int [] = Some []，但走 all_int 分支会得到 None（Some nil => None），总之与 Some v 冲突 *)
              (* 最稳：直接用 Hrs 把 all_real 也写进去，让 H 化成 None = Some v *)
              (* 先把 Hrs 具体化： *)
              simpl in Hrs. inversion Hrs; subst rs.
              (* 现在 H 是 aggop_sem AggMin [] = Some v，展开后必为 None *)
              (* 具体化展开： *)
              unfold aggop_sem in H; simpl in H.
              (* 这里一般会出现 None = Some v *)
              inversion H.
          
            ++ (* xs = v0 :: xs' *)
              (* all_int (v0::xs') = None，因为 v0 是 Ty_Real *)
              pose proof (all_int_none_of_all_real_cons M v0 xs'
                          (Forall_inv HallReal)) as HintNone.
              unfold aggop_sem in H; simpl in H.
              simpl in Hrs.
              destruct (all_real xs') as [rs'|] eqn:Har; simpl in Hrs; try discriminate.
              ** 
                (* v0 必为 V_Real r0 *)
                destruct (vhas_type_real_inv M v0 (Forall_inv HallReal)) as [r0 Hr0].
                subst v0.
                (* 反演并结束 *)
                inversion H; subst.
                constructor.
              **
                (* v0 必为 V_Real r0 *)
                destruct (vhas_type_real_inv M v0 (Forall_inv HallReal)) as [r0 Hr0].
                subst v0.
                (* 反演并结束 *)
                inversion H; subst.
          -- (* ================= AggMax : Ty_Real ================= *)
            destruct xs as [|v0 xs'].
            ++ (* xs = [] *)
              simpl in Hrs. inversion Hrs; subst rs.
              unfold aggop_sem in H; simpl in H.
              inversion H.
            ++ (* 0) 先得到 all_int (v0::xs') = None （因为 v0 是 Ty_Real） *)
              pose proof (all_int_none_of_all_real_cons M v0 xs' (Forall_inv HallReal)) as HintNone.
              
              (* 1) 把 v0 化成 V_Real r0，方便对 Hrs 分解 *)
              destruct (vhas_type_real_inv M v0 (Forall_inv HallReal)) as [r0 Hr0].
              subst v0.
              
              (* 2) 从 Hrs: all_real (V_Real r0 :: xs') = Some rs 反推出 all_real xs' = Some rs' *)
              simpl in Hrs.
              destruct (all_real xs') as [rs'|] eqn:Har; simpl in Hrs; try discriminate.
              inversion Hrs; subst rs.
              
              (* 3) 展开 aggop_sem AggMax，并用 HintNone、Har 化简 *)
              unfold aggop_sem in H; simpl in H.
              rewrite Har in H.
              inversion H; subst.
              constructor.
              
          
          -- (* ================= AggSum : Ty_Real ================= *)
            destruct xs as [|v0 xs'].
            ++ (* xs = [] *)
              unfold aggop_sem in H; simpl in H. inversion H.
          
            ++ (* 0) 取出 v0 的实数形态 *)
              destruct (vhas_type_real_inv M v0 (Forall_inv HallReal)) as [r0 Hr0].
              subst v0.
              
              (* 1) int 分支必失败 *)
              pose proof (all_int_none_of_all_real_cons M (V_Real r0) xs'
                            (Forall_inv HallReal)) as HintNone.
              (* 上面这行如果类型不对，就改成： 
                pose proof (all_int_none_of_all_real_cons M (V_Real r0) xs' (VHT_Real ...)) 
                关键是得到 all_int (V_Real r0 :: xs') = None
              *)
              
              (* 2) 从 Hrs 拆出尾部 all_real xs' = Some rs' *)
              simpl in Hrs.
              destruct (all_real xs') as [rs'|] eqn:Har; simpl in Hrs; try discriminate.
              inversion Hrs; subst rs.
              
              (* 3) 展开 AggSum 的语义并化简到 real 分支 *)
              unfold aggop_sem in H; simpl in H.
              rewrite Har in H.
              inversion H; subst.
              constructor.



  Qed.
  







(* 

 Lemma preservation_bagliteral :
 forall Gamma M E ts vs T,
   env_has_type Gamma E ->
   (forall t, In t ts -> has_type Gamma t T) ->
   E_BagLiteral M E ts vs ->
   forall v, In v vs -> vhas_type v T.
Proof.
 intros Gamma M E ts vs T Henv Hts Hevts.
 induction Hevts.
 - (* E_BagLitNil: ts=[] vs=[] *)
   intros v Hin. inversion Hin.
 - (* E_BagLitCons: ts=t::tl vs=v::vl *)
   intros v0 Hin.
   simpl in Hin. destruct Hin as [Heq | Hin'].
   + subst v0.
     (* 用外层的 preservation_bigstep（或你当前 theorem 的可用版本）去处理 cevalR M E t v *)
     (* 需要：has_type Gamma t T *)
     apply (preservation_bigstep Gamma M E t v T); try assumption.
     * apply Hts. simpl. left. reflexivity.
     * assumption.  (* cevalR 前提来自 E_BagLiteralCons 构造子里 *)
   + (* v0 在尾部 vl *)
     apply IHHevts.
     * intros t0 HIn0. apply Hts. simpl. right. exact HIn0.
     * exact Hin'.
Qed. *)


