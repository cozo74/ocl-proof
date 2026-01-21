From Stdlib Require Import String ZArith Reals List.
Import ListNotations.

Open Scope string_scope.


(*************************************************************)
(*                    命名                         *)
(*************************************************************)


(* 统一使用 string 表示名字 *)
Definition class_name := string.
Definition assoc_name := string.
Definition attr_name  := string.
Definition role_name  := string.


(* 对象标识符 *)
Definition oid := string.

(*************************************************************)
(*           Object Model 中的类型与Instance domain           *)
(*************************************************************)


(* 类型 *)
(*  Basic type *)
Inductive T_b : Type :=
  | Tb_Bool
  | Tb_Int
  | Tb_Real
  | Tb_String.


(* T_hat = T_b \cup T_c *)
Inductive T_h : Type :=
  | Th_Basic: T_b -> T_h
  | Th_Object : class_name -> T_h.


(* T_expr *)
Inductive T_e : Type :=
  | Te_Single : T_h -> T_e
  | Te_Bag : T_h -> T_e.




(* Instance domain *)

Inductive I_b : Type :=
  | Ib_Int    : Z -> I_b
  | Ib_Real   : R -> I_b
  | Ib_Bool   : bool -> I_b
  | Ib_String : string -> I_b.


(* I_hat *)
Inductive I_h : Type :=
  | Ih_Basic    : I_b -> I_h
  | Ih_Object    : oid -> I_h.

(* I_expr *)
Inductive I_e : Type :=
  | Ie_Single : I_h -> I_e
  | Ie_Bag    : T_h -> list I_h -> I_e.








(*************************************************************)
(*                    Object Model 的定义                     *)
(*************************************************************)



 

(* Object Model 中的属性 = 属性名 + 属性类型 *)
Record attr_sig : Type := {
  att_name : string;
  att_type   : T_b
}.


(* option nat = upper bound, None = * *)
Inductive Multiplicity : Type :=
  | One     (* 1 *)
  | Many.  (* {1..n} - {1} <> {} *)



Record assoc_pair : Type := {
  c1 : class_name;
  c2 : class_name;
}.

Record role_pair : Type := {
  r1 : role_name;
  r2 : role_name;
  role_name_distinct : r1 <> r2
}.

Record multi_pair : Type := {
  m1 : Multiplicity;
  m2 : Multiplicity;
}.








Record object_model_data : Type := {

  (*  a set of classes  *)
  CLASS : list class_name;

  (*  a set of operation signatures for functions mapping an object of class c  *)
  ATT_c : class_name -> option (list attr_sig);

  (*  a set of association names  *)
  ASSOC : list assoc_name;

  (*  a function mapping each association name to a list of participating classes  *)
  associates : assoc_name -> option assoc_pair;

  (*  a function assigning each end of an association a role name  *)
  roles : assoc_name -> option role_pair;

  (* a function assigning each end of an association a multiplicity specification *)
  multiplicities : assoc_name -> option multi_pair;


}.




  (* gives the set of all role names reachable (or navigable) from a class over a given association. *)
  Definition navends_ca (M : object_model_data) (c : class_name) (asso : assoc_name) : option (list role_name) :=
    match associates M asso, roles M asso with
    | Some ap, Some rp =>
        if String.string_dec (c1 ap) c then Some [r2 rp]
        else if String.string_dec (c2 ap) c then Some [r1 rp]
        else Some []
    | _, _ => None
    end.


  Definition option_list_to_list {A} (o : option (list A)) : list A :=
    match o with
    | Some xs => xs
    | None => []
    end.
  

  (* The set of role names that are reachable from a class along all associations the class participates in *)
  Definition navends_c (M : object_model_data) (c : class_name) : list role_name :=
    flat_map
      (fun asso => option_list_to_list (navends_ca M c asso))
      (ASSOC M).



  Definition disjoint_strings (xs ys : list string) : Prop :=
    (forall n, In n xs -> ~ In n ys) /\
    (forall n, In n ys -> ~ In n xs).
    
  
  Definition attr_names_of (M : object_model_data) (c : class_name) : list string :=
    match ATT_c M c with
    | Some attrs => map att_name attrs
    | None => []
    end.
  

  Record object_model : Type := {
    data : object_model_data;
  


    (* ===================== *)
    (* well-formedness props *)
    (* ===================== *)

    wf_CLASS_nodup : NoDup (CLASS data);
    wf_ASSOC_nodup : NoDup (ASSOC data);

    wf_CLASS_ASSOC_disjoint :
      disjoint_strings (CLASS data) (ASSOC data);

    (* 属性表：c ∈ CLASS <-> ATT_c c = Some ... *)
    wf_ATT_defined_iff :
      forall c,
        In c (CLASS data) <-> exists attrs, (ATT_c data) c = Some attrs;

    (* associates：as ∈ ASSOC <-> associates as = Some ... *)
    wf_assoc_defined_iff :
    forall asso,
      In asso (ASSOC data) <-> exists ap, (associates data) asso  = Some ap;

    (* roles：as ∈ ASSOC <-> roles as = Some ... *)
    wf_roles_defined_iff :
      forall asso,
        In asso (ASSOC data) <-> exists rp, (roles data) asso = Some rp;

    (* multiplicities：as ∈ ASSOC <-> multiplicities as = Some ... *)
    wf_mult_defined_iff :
      forall asso,
        In asso (ASSOC data) <-> exists mp, (multiplicities data) asso = Some mp;

    (* --- 端点合法：association 的端点类必须属于 CLASS --- *)
    wf_assoc_endpoints_in_CLASS :
      forall asso ap,
        (associates data) asso = Some ap ->
        In (c1 ap) (CLASS data) /\ In (c2 ap) (CLASS data);


    (* --- 属性名唯一：同一类内属性名不重复 --- *)
    wf_attr_names_nodup :
      forall c attrs,
        (ATT_c  data) c = Some attrs ->
        NoDup (map att_name attrs);


    (* --- 角色名唯一：同一类内角色名不重复 --- *)
    wf_role_names_unique_per_class :
    forall c, In c (CLASS data) ->
      NoDup (navends_c data c);

    (* --- 属性名和角色名都唯一：同一类内属性名和角色名都不重复 --- *)
    wf_attr_and_role_names_disjoint_per_class :
      forall c, In c (CLASS data) ->
        disjoint_strings (attr_names_of data c) (navends_c data c);


  }.








(*************************************************************)
(*                   SystemState 系统状态                     *)
(*************************************************************)


(* ========== oid-space：抽象化 oid(c) ========== *)
Definition oid_of := class_name -> oid -> Prop.

(* ========== multiplicity 语义（你目前只有 One/Many） ========== *)
Definition sat_mult (m : Multiplicity) (k : nat) : Prop :=
  match m with
  | One  => k = 1
  | Many => 1 <= k
  end.

(* ========== 二元 association 的投影 ========== *)
Definition pi1_link (l : oid * oid) : oid := fst l.
Definition pi2_link (l : oid * oid) : oid := snd l.


(* bar_pi_i：投影“除第 i 个分量之外的所有分量”
二元情况下：bar_pi1(l)=snd l, bar_pi2(l)=fst l *)
Definition bar_pi1 (l : oid * oid) : oid := snd l.
Definition bar_pi2 (l : oid * oid) : oid := fst l.

(* ========== 计数：在 link 集合中，与 l 在 bar_pi_i 上相同的链接个数 ========== *)
Definition count_same_bar1 (links : list (oid * oid)) (l : oid * oid) : nat :=
  length (filter (fun l' => String.eqb (bar_pi1 l') (bar_pi1 l)) links).


Definition count_same_bar2 (links : list (oid * oid)) (l : oid * oid) : nat :=
  length (filter (fun l' => String.eqb (bar_pi2 l') (bar_pi2 l)) links).



Record system_state_data : Type := {
  (* σ_CLASS : CLASS -> finite set of oids *)
  sigma_CLASS : class_name -> option (list oid);

  (* σ_ATT : 给对象的属性赋值（部分函数），以 option 表达未定义 *)
  sigma_ATT : class_name -> oid -> string -> option I_b;

  (* σ_ASSOC : ASSOC -> finite set of links (oid*oid) *)
  sigma_ASSOC : assoc_name -> option (list (oid * oid));
}.




Record system_state (M : object_model) (oidSpace : oid_of) : Type := {
  st : system_state_data;

  (* i) σ_CLASS(c) 是有限集合，且 c ∈ CLASS <-> 有定义 *)
  wf_sigma_CLASS_defined_iff :
    forall c,
      In c (CLASS (data M)) <-> exists os, (sigma_CLASS st) c = Some os;

  wf_sigma_CLASS_nodup :
    forall c os,
      sigma_CLASS st c = Some os ->
      NoDup os;

  (* σ_CLASS(c) ⊂ oid(c) *)
  wf_sigma_CLASS_subset_oid :
    forall c os o,
      sigma_CLASS st c = Some os ->
      In o os ->
      oidSpace c o;




  (* ii) σ_ATT(c,o,a) 有定义  <->  o ∈ σ_CLASS(c) 且 a 是 c 的属性名 *) 

  wf_sigma_ATT_defined_iff :
    forall c o a,
      (sigma_ATT st) c o a <> None <->
      exists attrs,
        (ATT_c (data M)) c = Some attrs /\
        In a (map att_name attrs) /\
        exists os,
          (sigma_CLASS st) c = Some os /\
          In o os;


  (* iii-a) σ_ASSOC(as) 有定义 <-> asso ∈ ASSOC(M) *)
  wf_sigma_ASSOC_defined_iff :
    forall asso,
      (sigma_ASSOC st) asso <> None <->
      In asso (ASSOC (data M));


  wf_sigma_ASSOC_nodup :
    forall asso ls,
      sigma_ASSOC st asso = Some ls ->
      NoDup ls;

  (* 
  associates asso = Some ap 给出端点类 c1 ap, c2 ap
  l = (o1,o2) ∈ σ_ASSOC(asso) 要求：
  o1 ∈ σ_CLASS(c1 ap) 且 o2 ∈ σ_CLASS(c2 ap)
  同时 oidSpace (c1 ap) o1、oidSpace (c2 ap) o2（可选，但建议保留）
  *)

  wf_links_endpoints_welltyped :
    forall asso ap ls l o1 o2,
      (associates (data M)) asso = Some ap ->
      sigma_ASSOC st asso = Some ls ->
      In l ls ->
      l = (o1, o2) ->
      exists os1 os2,
        sigma_CLASS st (c1 ap) = Some os1 /\
        sigma_CLASS st (c2 ap) = Some os2 /\
        In o1 os1 /\ In o2 os2 /\
        oidSpace (c1 ap) o1 /\ oidSpace (c2 ap) o2;

  (* 
  规范的式子（对二元关联）可以解释为：
  对每个 l = (o1,o2)：
  固定 o2，统计与它相连的 o1 的数量，应满足端点 1 的 multiplicity：m1
  固定 o1，统计与它相连的 o2 的数量，应满足端点 2 的 multiplicity：m2
  *)
  wf_multiplicity_constraints :
    forall asso mp ls l,
      (multiplicities (data M)) asso = Some mp ->
      sigma_ASSOC st asso = Some ls ->
      In l ls ->
      sat_mult (m1 mp) (count_same_bar1 ls l) /\
      sat_mult (m2 mp) (count_same_bar2 ls l);

}.












(*************************************************************)
(*                   关系 Schema 定义                         *)
(*************************************************************)

(* 数据库列类型 *)
Inductive T_ra : Type :=
  | Tra_Bool
  | Tra_Int
  | Tra_Real
  | Tra_String
  | Tra_Object (C : class_name).   (* 对象标识符，指向类 C *)


Inductive I_ra : Type :=
  | Ira_Bool : bool -> I_ra
  | Ira_Int : Z -> I_ra
  | Ira_Real : R -> I_ra
  | Ira_String : string -> I_ra
  | Ira_Object : oid -> I_ra. 




(* 值与类型匹配 *)
Definition I_ra_has_type (oidSpace : oid_of) (v : I_ra) (t : T_ra) : Prop :=
  match v, t with
  | Ira_Bool _,   Tra_Bool        => True
  | Ira_Int _,    Tra_Int         => True
  | Ira_Real _,   Tra_Real        => True
  | Ira_String _, Tra_String      => True
  | Ira_Object o, Tra_Object C    => oidSpace C o
  | _, _ => False
  end.




(* 数据库列 *)
Record Column : Type := {
  col_name : string;
  col_ty   : T_ra
}.

(* 数据库表 Schema *)
Record TableSchema : Type := {
  table_name : string;
  table_cols : list Column

}.

(* 整个数据库 Schema *)
Definition Schema := list TableSchema.




(*************************************************************)
(*                数据库实例 DBInstance 定义                   *)
(*************************************************************)

Definition RowData : Type := list (string * I_ra).




Definition TableInstRaw : Type := list RowData.

Record DBInstanceRaw : Type := {
  tables : string -> option (list RowData)
}.







(*************************************************************)
(*        ObjectModel 类 → 数据库 Schema 的转换规则             *)
(*************************************************************)


(* 类型与值的映射 *)
(* ---------- type mapping: T_b -> T_ra ---------- *)
Definition enc_Tb (t : T_b) : T_ra :=
  match t with
  | Tb_Bool   => Tra_Bool
  | Tb_Int    => Tra_Int
  | Tb_Real   => Tra_Real
  | Tb_String => Tra_String
  end.

(* ---------- value mapping: I_b -> I_ra ---------- *)
Definition enc_Ib (v : I_b) : I_ra :=
  match v with
  | Ib_Bool b   => Ira_Bool b
  | Ib_Int z    => Ira_Int z
  | Ib_Real r   => Ira_Real r
  | Ib_String s => Ira_String s
  end.


  (* 表名与列名约定 *)
Definition oid_col : string := "oid".

Definition tbl_class (c : class_name) : string := c.
Definition tbl_assoc (asso : assoc_name) : string := asso.


(* 生成 Class 表 schema *)
Definition col_oid (c : class_name) : Column :=
  {| col_name := oid_col; col_ty := Tra_Object c |}.

Definition col_of_attr (a : attr_sig) : Column :=
  {| col_name := att_name a; col_ty := enc_Tb (att_type a) |}.

Definition class_table_schema (M : object_model) (c : class_name) : TableSchema :=
  match (ATT_c (data M)) c with
  | Some attrs =>
      {| table_name := tbl_class c
       ; table_cols := col_oid c :: map col_of_attr attrs |}
  | None =>
      (* 在良构 object_model 下该分支对 In c CLASS 不应出现；
         这里给一个防御性默认值 *)
      {| table_name := tbl_class c
       ; table_cols := [col_oid c] |}
  end.



(* 生成 Assoc 表 schema（二元关联） *)

Definition assoc_table_schema (M : object_model) (asso : assoc_name) : TableSchema :=
  match associates (data M) asso, roles (data M) asso with
  | Some ap, Some rp =>
      {| table_name := tbl_assoc asso
       ; table_cols :=
           [ {| col_name := r1 rp; col_ty := Tra_Object (c1 ap) |}
           ; {| col_name := r2 rp; col_ty := Tra_Object (c2 ap) |} ] |}
  | _, _ =>
      (* 良构模型下 as∈ASSOC 时不应发生；防御性默认 *)
      {| table_name := tbl_assoc asso; table_cols := [] |}
  end.


(* 总 Schema *)
Definition enc_schema (M : object_model) : Schema :=
  List.app (map (class_table_schema M) (CLASS (data M))) (map (assoc_table_schema M) (ASSOC (data M))).





  



(*************************************************************)
(*           SystemState → DBInstance 的转换规则               *)
(*************************************************************)



(* ---------- 1) 构造 class 表中的一行（稀疏：缺属性就不写该列） ---------- *)
Definition mk_class_row_sparse
  (S : system_state_data) (c : class_name) (attrs : list attr_sig) (o : oid)
  : RowData :=
  (oid_col, Ira_Object o)
  ::
  fold_right
    (fun a acc =>
       match sigma_ATT S c o (att_name a) with
       | Some vb => (att_name a, enc_Ib vb) :: acc
       | None => acc
       end)
    []
    attrs.



(* ---------- 2) 构造 assoc 表中的一行 ---------- *)
Definition mk_assoc_row_data (rp : role_pair) (l : oid * oid) : RowData :=
  [ (r1 rp, Ira_Object (fst l))
  ; (r2 rp, Ira_Object (snd l)) ].




(* ---------- 3) 生成某个 class 表的实例 ---------- *)
Definition class_table_inst_raw
  (M : object_model) (S : system_state_data) (c : class_name)
  : option (list RowData) :=
  match sigma_CLASS S c with
  | None => None
  | Some os =>
      let attrs :=
        match ATT_c (data M) c with
        | Some asigs => asigs
        | None => []   (* 防御：无属性声明就只写 oid *)
        end
      in
      Some (map (fun o => mk_class_row_sparse S c attrs o) os)
  end.




  
(* ---------- 4) 生成某个 assoc 表的实例 ---------- *)
Definition assoc_table_inst_raw
  (M : object_model) (S : system_state_data) (asso : assoc_name)
  : option (list RowData) :=
  match sigma_ASSOC S asso, roles (data M) asso with
  | Some ls, Some rp =>
      Some (map (mk_assoc_row_data rp) ls)
  | _, _ => None
  end.

(* ---------- 5) 最终编码：SystemState -> DBInstanceRaw ---------- *)
Definition enc_db_raw (M : object_model) (S : system_state_data) : DBInstanceRaw :=
  {| tables :=
       fun tname =>
         (* 先尝试 class 表 *)
         if in_dec String.string_dec tname (CLASS (data M)) then
           class_table_inst_raw M S tname
         else if in_dec String.string_dec tname (ASSOC (data M)) then
           assoc_table_inst_raw M S tname
         else
           None
  |}.

