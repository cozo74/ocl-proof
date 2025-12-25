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
      vhas_type M v T
  with preservation_bagliteral :
    forall Gamma M E ts vs T,
      env_has_type Gamma M E ->
      (forall t, In t ts -> has_type Gamma t T) ->
      E_BagLiteral M E ts vs ->
      forall v, In v vs -> vhas_type M v T.
  Proof.
    - (* preservation_bigstep *)
      intros Gamma M E t v T Hmodel Henv Hty Hev.
      revert T Hty.
      induction Hev; intros T0 Hty; try solve_simple_con.
      + intros v HIn. inversion HIn.
      + intros v Hin. eapply preservation_bagliteral; eauto.
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
      +

        
        











        
    - (* preservation_bagliteral *)
      intros Gamma M E ts vs T Henv Hts Hevts.
      induction Hevts; (* 如上面的证明结构 *)
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


