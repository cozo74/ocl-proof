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


Definition Schema_data : Type := list TableSchema.





(* TableSchema 良构：列名唯一 *)
Definition wf_TableSchema (ts : TableSchema) : Prop :=
  NoDup (map col_name (table_cols ts)).



(* Schema 良构：表名唯一 + 每张表列名唯一 *)
Definition wf_Schema (sc : Schema_data) : Prop :=
  NoDup (map table_name sc) /\
  Forall wf_TableSchema sc.




Record Schema : Type := {
  sc_data : Schema_data;
  sc_wf   : wf_Schema sc_data
}.






(*************************************************************)
(*                数据库实例 DBInstance 定义                   *)
(*************************************************************)





Definition RowData : Type := list (string * I_ra).



Record DBInstance_data : Type := {
  db_tables : string -> option (list RowData)
}.



(* 辅助函数：从 RowData 查列值 *)
Fixpoint lookup_row (cn : string) (r : RowData) : option I_ra :=
  match r with
  | [] => None
  | (k,v)::tl => if String.string_dec k cn then Some v else lookup_row cn tl
  end.


(* 辅助函数：从Schema 中查表” *)
Fixpoint lookup_table (sc : Schema_data) (tname : string) : option TableSchema :=
  match sc with
  | [] => None
  | ts :: tl =>
      if String.string_dec (table_name ts) tname then Some ts else lookup_table tl tname
  end.


(* 严格行（域精确等于表列集合） *)
Definition row_domain (r : RowData) : list string :=
  map fst r.




(* Row 严格良构：域=列集合 + 行内无重复 + 类型匹配 *)
Definition wf_Row_strict (oidSpace : oid_of) (ts : TableSchema) (r : RowData) : Prop :=
  NoDup (row_domain r) /\
  (forall cn,
      In cn (row_domain r) <->
      exists col, In col (table_cols ts) /\ col_name col = cn) /\
  (forall col v,
      In col (table_cols ts) ->
      lookup_row (col_name col) r = Some v ->
      I_ra_has_type oidSpace v (col_ty col)).

Definition wf_TableInst (oidSpace : oid_of) (ts : TableSchema) (rows : list RowData) : Prop :=
  Forall (wf_Row_strict oidSpace ts) rows.





(* DBInstance 总 wf：域受 Schema 限制 + 每张表实例良构 *)
Definition wf_DBInstance (oidSpace : oid_of) (sc : Schema_data) (db : DBInstance_data) : Prop :=
  let tbl := db_tables db in
  (* 表有定义 -> schema 里确实存在该表 *)
  (forall tname rows,
      tbl tname = Some rows ->
      exists ts, lookup_table sc tname = Some ts)
  /\
  (* 对 schema 中每张表：若 db 有实例，则实例必须符合表结构 *)
  (forall tname ts rows,
      lookup_table sc tname = Some ts ->
      tbl tname = Some rows ->
      wf_TableInst oidSpace ts rows).





Record DBInstance (oidSpace : oid_of) (SC : Schema) : Type := {
  db_data : DBInstance_data;
  db_wf   : wf_DBInstance oidSpace (sc_data SC) db_data
}.













(*************************************************************)
(*        ObjectModel 类 → 数据库 Schema 的对应关系             *)
(*************************************************************)



(* 常量：类表的 oid 列名 *)
Definition oid_col : string := "oid".

(* 将 basic type 映射到 RA 列类型 *)
Definition enc_Tb (t : T_b) : T_ra :=
  match t with
  | Tb_Bool   => Tra_Bool
  | Tb_Int    => Tra_Int
  | Tb_Real   => Tra_Real
  | Tb_String => Tra_String
  end.

(* 在表中按列名查找列 *)
Fixpoint lookup_col (cn : string) (cols : list Column) : option Column :=
  match cols with
  | [] => None
  | c :: tl =>
      if String.string_dec (col_name c) cn then Some c else lookup_col cn tl
  end.

(* 在 schema 中按表名查找表 *)
Fixpoint lookup_tableS (sc : Schema_data) (tname : string) : option TableSchema :=
  match sc with
  | [] => None
  | ts :: tl =>
      if String.string_dec (table_name ts) tname then Some ts else lookup_tableS tl tname
  end.


(* 
一个类 c 对应一张表 ts，满足：
  - table_name ts = c
  - oid 列存在且类型为 Tra_Object c
  - 对 ATT_c c 中每个属性 a：存在同名列，类型是 enc_Tb (att_type a)

*)
Definition ClassTable_ok (M : object_model) (c : class_name) (ts : TableSchema) : Prop :=
  table_name ts = c /\
  (* oid 列 *)
  exists col_oid,
    lookup_col oid_col (table_cols ts) = Some col_oid /\
    col_ty col_oid = Tra_Object c /\
  (* 属性列 *)
  (forall attrs a,
      ATT_c (data M) c = Some attrs ->
      In a attrs ->
      exists col_a,
        lookup_col (att_name a) (table_cols ts) = Some col_a /\
        col_ty col_a = enc_Tb (att_type a)).


(* 无多余列：  表中的列集合恰好等于 oid + 属性列集合（不多不少，类型是 enc_Tb (att_type a) *)
Definition ClassTable_no_extra_cols (M : object_model) (c : class_name) (ts : TableSchema) : Prop :=
  forall cn col,
    lookup_col cn (table_cols ts) = Some col ->
    cn = oid_col \/
    exists attrs a,
      ATT_c (data M) c = Some attrs /\
      In a attrs /\
      cn = att_name a.


(* 
二元关联 asso 对应一张表 ts，满足：
  - table_name ts = asso
  - 若 associates asso = <c1,c2> 且 roles asso = <r1,r2>：
  - 表包含列 r1 : Tra_Object c1
  - 表包含列 r2 : Tra_Object c2
*)
Definition AssocTable_ok (M : object_model) (asso : assoc_name) (ts : TableSchema) : Prop :=
  table_name ts = asso /\
  exists ap rp,
    associates (data M) asso = Some ap /\
    roles (data M) asso = Some rp /\
    (* role r1 列 *)
    exists col1,
      lookup_col (r1 rp) (table_cols ts) = Some col1 /\
      col_ty col1 = Tra_Object (c1 ap) /\
    (* role r2 列 *)
    exists col2,
      lookup_col (r2 rp) (table_cols ts) = Some col2 /\
      col_ty col2 = Tra_Object (c2 ap).


Definition AssocTable_no_extra_cols (M : object_model) (asso : assoc_name) (ts : TableSchema) : Prop :=
  forall cn col,
    lookup_col cn (table_cols ts) = Some col ->
    exists ap rp,
      associates (data M) asso = Some ap /\
      roles (data M) asso = Some rp /\
      (cn = r1 rp \/ cn = r2 rp).

    


(* 
- 对每个 c ∈ CLASS(M)：schema 里存在表名为 c 的表，满足 ClassTable_ok
- 对每个 asso ∈ ASSOC(M)：schema 里存在表名为 asso 的表，满足 AssocTable_ok
- （可选）schema 中的每张表名要么是类名要么是关联名（不多余表）
*)
Definition EncSchema (M : object_model) (sc : Schema_data) : Prop :=
  (* 每个类都有对应表 *)
  (forall c,
      In c (CLASS (data M)) ->
      exists ts,
        lookup_tableS sc c = Some ts /\
        ClassTable_ok M c ts)
  /\
  (* 每个关联都有对应表 *)
  (forall asso,
      In asso (ASSOC (data M)) ->
      exists ts,
        lookup_tableS sc asso = Some ts /\
        AssocTable_ok M asso ts)
  /\
  (* 可选：schema 不包含额外表 *)
  (forall tname ts,
      lookup_tableS sc tname = Some ts ->
      In tname (CLASS (data M)) \/ In tname (ASSOC (data M))).




Definition EncSchemaW (M : object_model) (SC : Schema) : Prop :=
  EncSchema M (sc_data SC).





  Definition ClassTable_ok_strong (M : object_model) (c : class_name) (ts : TableSchema) : Prop :=
  ClassTable_ok M c ts /\ ClassTable_no_extra_cols M c ts.

Definition AssocTable_ok_strong (M : object_model) (asso : assoc_name) (ts : TableSchema) : Prop :=
  AssocTable_ok M asso ts /\ AssocTable_no_extra_cols M asso ts.

Definition EncSchema_strong (M : object_model) (sc : Schema_data) : Prop :=
  (* 每个类都有对应表（且列不多不少） *)
  (forall c,
      In c (CLASS (data M)) ->
      exists ts,
        lookup_tableS sc c = Some ts /\
        ClassTable_ok_strong M c ts)
  /\
  (* 每个关联都有对应表（且列不多不少） *)
  (forall asso,
      In asso (ASSOC (data M)) ->
      exists ts,
        lookup_tableS sc asso = Some ts /\
        AssocTable_ok_strong M asso ts)
  /\
  (* schema 不包含额外表 *)
  (forall tname ts,
      lookup_tableS sc tname = Some ts ->
      In tname (CLASS (data M)) \/ In tname (ASSOC (data M))).




Definition EncSchemaW_strong (M : object_model) (SC : Schema) : Prop :=
  EncSchema_strong M (sc_data SC).








(*************************************************************)
(*           SystemState → DBInstance 的对应关系               *)
(*************************************************************)

(* I_b -> I_ra *)
Definition enc_Ib (v : I_b) : I_ra :=
  match v with
  | Ib_Bool b   => Ira_Bool b
  | Ib_Int z    => Ira_Int z
  | Ib_Real r   => Ira_Real r
  | Ib_String s => Ira_String s
  end.




Definition ClassObjectRow_ok
  (M : object_model)
  (S : system_state_data)
  (c : class_name)
  (o : oid)
  (r : RowData) : Prop :=

  (* oid 列 *)
  lookup_row oid_col r = Some (Ira_Object o)
  /\
  (* 属性列 *)
  (forall attrs a v,
      ATT_c (data M) c = Some attrs ->
      In a attrs ->
      sigma_ATT S c o (att_name a) = Some v ->
      lookup_row (att_name a) r = Some (enc_Ib v))
  /\
  (* 不出现“幽灵属性列” *)
  (forall cn v,
      lookup_row cn r = Some v ->
      cn = oid_col \/
      exists attrs a,
        ATT_c (data M) c = Some attrs /\
        In a attrs /\
        cn = att_name a).




Definition ClassTableInst_ok
  (M : object_model)
  (S : system_state_data)
  (c : class_name)
  (rows : list RowData) : Prop :=

  (* 覆盖性：每个对象都有一行 *)
  (forall o os,
      sigma_CLASS S c = Some os ->
      In o os ->
      exists r, In r rows /\ ClassObjectRow_ok M S c o r)
  /\
  (* 反向性：每行来自某个对象 *)
  (forall r,
      In r rows ->
      exists o os,
        sigma_CLASS S c = Some os /\
        In o os /\
        ClassObjectRow_ok M S c o r).
      


Definition AssocLinkRow_ok
  (M : object_model)
  (asso : assoc_name)
  (l : oid * oid)
  (r : RowData) : Prop :=

  exists rp,
    roles (data M) asso = Some rp /\
    lookup_row (r1 rp) r = Some (Ira_Object (fst l)) /\
    lookup_row (r2 rp) r = Some (Ira_Object (snd l)).



Definition AssocTableInst_ok
  (M : object_model)
  (S : system_state_data)
  (asso : assoc_name)
  (rows : list RowData) : Prop :=

  (* 覆盖性 *)
  (forall l ls,
      sigma_ASSOC S asso = Some ls ->
      In l ls ->
      exists r, In r rows /\ AssocLinkRow_ok M asso l r)
  /\
  (* 反向性 *)
  (forall r,
      In r rows ->
      exists l ls,
        sigma_ASSOC S asso = Some ls /\
        In l ls /\
        AssocLinkRow_ok M asso l r).




Definition EncDB
  (M : object_model)
  (S : system_state_data)
  (sc : Schema_data)
  (db : DBInstance_data) : Prop :=

  (* 类表一致 *)
  (forall c ts rows,
      In c (CLASS (data M)) ->
      lookup_table sc c = Some ts ->
      db_tables db c = Some rows ->
      ClassTableInst_ok M S c rows)
  /\
  (* 关联表一致 *)
  (forall asso ts rows,
      In asso (ASSOC (data M)) ->
      lookup_table sc asso = Some ts ->
      db_tables db asso = Some rows ->
      AssocTableInst_ok M S asso rows).



Definition EncDBW
  (M : object_model)
  (oidSpace : oid_of)
  (SS : system_state M oidSpace)
  (SC : Schema)
  (DB : DBInstance oidSpace SC) : Prop :=
  EncDB M (st M oidSpace SS) (sc_data SC) ( db_data oidSpace SC DB).

