theory Incomplete_Criteria
imports "../Sloped_Graphs"
begin


(* 1. THE SPRENGER-DAM CRITERION *)

context Sloped_Graph
begin

(* A subgraph (Node1,edge1) satisfies the descent property with respect to a labelling of its nodes
if any edge is matched by a Main or Decrease RR-edge with the considered labels, 
and there is at least one Decr RR-edge. 
*)  

(* Descending height-change choice : *)
definition decreasingHCC :: "'node set \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> bool) \<Rightarrow> ('node \<Rightarrow> 'pos) \<Rightarrow> bool" where 
"decreasingHCC Node1 edge1 lab \<equiv> 
  (\<forall>nd nd'. edge1 nd nd' \<longrightarrow> RR (nd,lab nd) (nd',lab nd') Main \<or> 
                             RR (nd,lab nd) (nd',lab nd') Decr) \<and> 
  (\<exists>nd nd'. edge1 nd nd' \<and> RR (nd,lab nd) (nd',lab nd') Decr)"


(* If a subgraph has the descent property w.r.t. a labeling function, 
then any ipath through it will always persist w.r.t. these labels: *)
lemma decreasingHCC_ipath_alw_holds2: 
assumes lab: "decreasingHCC Node1 edge1 lab" and nds: "Graph.ipath Node1 edge1 nds"
shows 
"alw (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Main \<or> RR (nd, P) (nd', P') Decr))
     (szip nds (smap lab nds))"
using assms unfolding Graph.ipath_iff_snth decreasingHCC_def
unfolding alw_holds2_iff_snth by auto

(* .. and if it additionally visits all nodes infinitely often, then it 
will also always eventually decrease: *)
lemma decreasingHCC_ipath_alw_ev_holds2: 
assumes lab: "decreasingHCC Node1 edge1 lab" and nds: "Graph.ipath Node1 edge1 nds" and 
"\<forall>nd nd'. edge1 nd nd' \<longrightarrow> alw (ev (holds2 (\<lambda>ndd ndd'. ndd = nd \<and> ndd' = nd'))) nds"
shows 
"alw (ev (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Decr))) 
   (szip nds (smap lab nds))"
using assms unfolding Graph.ipath_iff_snth decreasingHCC_def
unfolding alw_ev_holds2_iff_snth by fastforce

lemma decreasingHCC_imp_descentIpath: 
assumes nds: "ipath nds"
and lim: "decreasingHCC (limitS nds) (limitR nds) lab"
shows "descentIpath nds (smap lab nds)"
proof-
  obtain i where 0: "Graph.ipath (limitS nds) (limitR nds) (sdrop i nds)" 
  using ipath_sdrop_limit[OF Node_finite nds] by auto
  show ?thesis 
  unfolding descentIpath_def apply(intro sdrop_evI[where m = i]) 
  unfolding sdrop_szip sdrop_smap  apply safe
    subgoal using decreasingHCC_ipath_alw_holds2[OF lim 0] .
    subgoal apply(rule decreasingHCC_ipath_alw_ev_holds2[OF lim 0])
    apply safe apply(rule alw_sdrop) unfolding limitR_def . .
  qed

(* Sprenger-Dam descent: *)
definition SDdescending :: bool where 
"SDdescending \<equiv> \<forall>Node1 edge1. scsg Node1 edge1 \<longrightarrow> (\<exists>lab. wfLabF Node1 lab \<and> decreasingHCC Node1 edge1 lab)"

proposition SDdescending_imp_InfiniteDescent: 
"SDdescending \<Longrightarrow> InfiniteDescent"
unfolding SDdescending_def InfiniteDescent_def 
using decreasingHCC_imp_descentIpath scsg_limit Node_finite by blast



(* 2. EXTENDED SPRENGER-DAM CRITERION  *)

definition "wfLabFS Node1 lab \<equiv> \<forall>nd\<in>Node1. lab nd \<noteq> {} \<and> lab nd \<subseteq> PosOf nd"

lemma wfLabFS_finite: "wfLabFS Node1 lab \<Longrightarrow> Node1 \<subseteq> Node \<Longrightarrow> nd\<in>Node1 \<Longrightarrow> finite (lab nd)" 
unfolding wfLabFS_def using infinite_super by (metis in_mono PosOf_finite)

lemma subgr_wfLabFS: 
"subgr Node1 edge1 S2 R2 \<Longrightarrow> wfLabFS S2 lab \<Longrightarrow> wfLabFS Node1 lab"
unfolding subgr_def subsetD wfLabFS_def by auto 

definition RRSetChoice :: 
"'node set \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> bool) \<Rightarrow> ('node \<Rightarrow> 'pos set) \<Rightarrow> 
('node \<Rightarrow> 'node \<Rightarrow> 'pos \<Rightarrow> 'pos) \<Rightarrow> bool" where 
"RRSetChoice Node1 edge1 lab f \<equiv> 
 (\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<longrightarrow> f nd nd' ` lab nd \<subseteq> lab nd') \<and>
 (\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> 
   (\<forall>P \<in> lab nd. RR (nd,P) (nd',f nd nd' P) Main \<or> RR (nd,P) (nd',f nd nd' P) Decr))"

(* The height-extended graph of a labeled SGSG: *)
definition "extgrS Node1 lab \<equiv> {(nd,P). nd \<in> Node1 \<and> P \<in> lab nd}"

definition "extgrR edge1 f \<equiv> 
   \<lambda>(nd,P) (nd',P'). edge1 nd nd' \<and> f nd nd' P = P'"


lemma finite_extgrS: 
assumes "finite Node1" "Node1 \<subseteq> Node" "wfLabFS Node1 lab"
shows "finite (extgrS Node1 lab)"
proof- 
  have 0: "extgrS Node1 lab = Sigma Node1 (\<lambda>nd. lab nd)" unfolding Sigma_def extgrS_def by auto
  show ?thesis unfolding 0 apply(rule finite_SigmaI)  
  using assms wfLabFS_finite by blast+
qed

(* Decreasing height-change set-choice: *)
definition decreasingHCSC :: 
"'node set \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> bool) \<Rightarrow> 
('node \<Rightarrow> 'pos set) \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> 'pos \<Rightarrow> 'pos) \<Rightarrow> bool" where 
"decreasingHCSC Node1 edge1 lab f \<equiv> 
 RRSetChoice Node1 edge1 lab f \<and> 
 (\<forall>NNode eedge. 
     Graph.subgr NNode eedge (extgrS Node1 lab) (extgrR edge1 f) \<and> 
     Graph.scg NNode eedge \<and>   
     (\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> 
               (\<exists>P P'. {(nd,P),(nd',P')} \<subseteq> NNode \<and> eedge (nd,P) (nd',P'))) 
     \<longrightarrow> 
     (\<exists>nd_P nd_P'. {nd_P,nd_P'} \<subseteq> NNode \<and> eedge nd_P nd_P' \<and> 
                   RR nd_P nd_P' Decr))"


(* Extended-Sprenger-Dam (XSD) descent: *)
definition XSDdescending :: bool where 
"XSDdescending \<equiv> \<forall>Node1 edge1. scsg Node1 edge1 \<longrightarrow> (\<exists>lab f. wfLabFS Node1 lab \<and> decreasingHCSC Node1 edge1 lab f)"

lemma decreasingHCSC_imp_descentIpath: 
assumes nds: "ipath nds" and lab: "wfLabFS (limitS nds) lab"
and lim: "decreasingHCSC (limitS nds) (limitR nds) lab f"
shows "\<exists>Ps. descentIpath nds Ps"
proof-
  define Node1 edge1 where Sedge1_def: "Node1 \<equiv> limitS nds" "edge1 \<equiv> limitR nds"
  obtain n where a: "alw (holdsS Node1 aand holds2 edge1) (sdrop n nds)" 
  using ipath_ev_alw[OF Node_finite nds] unfolding ev_iff_sdrop Sedge1_def by auto

  define nnds where "nnds \<equiv> sdrop n nds"

  have lndss: "limitR nds = limitR nnds" unfolding nnds_def by auto

  have nnds: "ipath nnds" by (simp add: Graph.ipath_sdrop nds nnds_def)
  have nnds_Sedge1: "\<forall>i. nnds!!i \<in> Node1 \<and> edge1 (nnds!!i) (nnds!!(Suc i))"
  using a unfolding nnds_def[symmetric] 
  using alw_holds2_iff_snth alw_holdsS_iff_snth alw_mono by blast

  obtain P0 where P0: "P0 \<in> lab (shd nnds)" 
    using lab unfolding wfLabFS_def 
    by (metis Sedge1_def(1) equals0I nnds_Sedge1 snth.simps(1))

  define Pi where "Pi \<equiv> rec_nat P0 (\<lambda>i P. f (nnds !! i) (nnds !! Suc i) P)"
  define Ps where "Ps \<equiv> fToStream Pi"

  have 00: "\<And>i. Pi i \<in> lab (nnds!!i) \<and> 
                edge1 (nnds !! i) (nnds !! Suc i) \<and> 
                Pi (Suc i) = f (nnds !! i) (nnds !! Suc i) (Pi i)"  
  subgoal for i apply(induct i) apply simp_all 
    subgoal using P0 unfolding Pi_def  
    by (metis (no_types, lifting) nnds_Sedge1 old.nat.simps(6) old.nat.simps(7) snth.simps(1))
    subgoal for i  unfolding Pi_def apply simp 
    by (smt (verit, best) Graph.limitR_S decreasingHCSC_def 
      RRSetChoice_def Node_finite Sedge1_def(2) image_subset_iff ipath_sdrop_limit lim 
       limitR_sdrop_eq nds nnds_Sedge1) . .

  hence 0: "\<And>i. Ps!!i \<in> lab (nnds!!i) \<and> Ps!!(Suc i) = f (nnds !! i) (nnds !! Suc i) (Ps !! i)"  
  by (simp add: Ps_def)
   
  define \<phi> where "\<phi> \<equiv> \<lambda>i P P'. P' \<in> lab(nnds!!(Suc i)) \<and> 
            (RR (nnds!!i,P) (nnds!!(Suc i),P') Main \<or> 
             RR (nnds!!i,P) (nnds!!(Suc i),P') Decr)" 
  have 2: "\<forall>i. \<phi> i (Pi i) (Pi (Suc i))" 
  using 0 unfolding \<phi>_def  
  by (smt (verit, best) "00" decreasingHCSC_def RRSetChoice_def 
         Sedge1_def(1) Sedge1_def(2) empty_subsetI insert_subset lim nnds_Sedge1) 

  have nnds_Ps: "Graph.ipath (extgrS Node1 lab) (extgrR edge1 f) (szip nnds Ps)"
  using 0 nnds_Sedge1 P0 unfolding Graph.ipath_iff_snth extgrS_def extgrR_def by auto

  have Node1: "finite Node1" "Node1 \<subseteq> Node" "wfLabFS Node1 lab" 
  unfolding Sedge1_def(1) using Node_finite infinite_super limitS_S 
  apply blast by (auto simp: Sedge1_def(1) limitS_S lab)  

  have eNode1: "finite (extgrS Node1 lab)" using finite_extgrS[OF Node1] .

  obtain nd P where nd_P: "(nd,P) \<in> extgrS Node1 lab" "\<forall>i. \<exists>j\<ge>i. nnds!!j = nd \<and> Ps!!j = P"
  using Graph.ipath_infinitely_often[OF eNode1 nnds_Ps] by auto

  have d_nnds: "descentIpath nnds Ps" 
  unfolding descentIpath_iff_snth2 apply(intro conjI)
    subgoal using 2 unfolding \<phi>_def by (simp add: Ps_def)
    subgoal proof safe
      fix i    
 
      obtain j0 where j0: "j0\<ge>i" "nnds!!j0 = nd \<and> Ps!!j0 = P" using nd_P by auto

      obtain j1 j2 where j12: "j1\<ge>Suc j0" "j2\<ge>j1" 
      "\<And>nd nd'. limitR nnds nd nd' \<Longrightarrow> (\<exists>j\<ge>j1. j < j2 \<and> nnds !! j = nd \<and> nnds !! Suc j = nd')"
      using ipath_limitR_interval[OF Node_finite nnds] by blast

      obtain j3 where j3: "j3\<ge>Suc j2" "nnds!!j3 = nd \<and> Ps!!j3 = P" using nd_P by auto

      define nd_Pl where "nd_Pl \<equiv> stake (j3-j0+1) (sdrop j0 (szip nnds Ps))"
      have cyc: "Graph.cycleG (extgrS Node1 lab) (extgrR edge1 f) nd_Pl" 
      unfolding nd_Pl_def apply(rule Graph.ipath_stake_sdrop_cycle) 
        subgoal by fact
        subgoal using j12(1) j12(2) j3(1) by linarith
        subgoal by simp (metis add_diff_cancel_left' add_leE j0(2) j12(1) j12(2) j3(1) j3(2) 
          nat_le_iff_add plus_1_eq_Suc) .
      
      define NNode where "NNode \<equiv> set (nd_Pl)"
      define eedge where "eedge \<equiv> \<lambda> nd_P nd_P'. 
      (\<exists>i. Suc i < length nd_Pl \<and> nd_P = nd_Pl!i \<and> nd_P' = nd_Pl!(Suc i))"

      have subgr: "Graph.subgr NNode eedge (extgrS Node1 lab) (extgrR edge1 f)"
      unfolding Graph.subgr_def NNode_def eedge_def set_conv_nth  
      using Graph.cycle_iff_nth cyc by blast

      have scg: "Graph.scg NNode eedge" apply(subst Graph.scg_iff_cycle)
        subgoal unfolding NNode_def by auto
        subgoal unfolding NNode_def 
        by simp (metis Graph.cycle_iff_nth cyc less_nat_zero_code list.size(3) 
         not_path_Nil path_iff_nth)
        subgoal apply(rule exI[of _ nd_Pl], standard)
          subgoal using cyc unfolding Graph.cycleG_def NNode_def eedge_def 
             unfolding Graph.path_iff_set_nth by auto
          subgoal unfolding NNode_def .. . .

      have "\<forall>nd nd'. edge1 nd nd' \<longrightarrow> 
        (\<exists>i<length nd_Pl - 1. \<exists>P P'. nd_Pl ! i = (nd, P) \<and> nd_Pl ! Suc i = (nd', P'))" 
      apply safe unfolding Sedge1_def lndss apply(drule j12(3)) apply safe
         subgoal for nd nd' j 
         apply(rule exI[of _ "j-j0"]) apply safe
           subgoal unfolding nd_Pl_def using j12(1) j3(1) by auto
           subgoal apply(rule exI[of _ "Ps!!j"]) apply(rule exI[of _ "Ps!!(Suc j)"])
           unfolding nd_Pl_def apply safe
             subgoal apply(subst stake_nth)
               subgoal using j3(1) by linarith
               subgoal unfolding sdrop_snth 
                 by (metis Suc_leD j12(1) le_add_diff_inverse le_trans snth_szip) .
             subgoal apply(subst stake_nth)
               subgoal using j3(1)j12(1) by linarith
               subgoal unfolding sdrop_snth 
                 by (metis Suc_leD add_Suc_right j12(1) le_add_diff_inverse le_trans snth_szip) . . . .  

      hence "(\<forall>nd nd'. edge1 nd nd' \<longrightarrow> 
               (\<exists>P P'. {(nd,P),(nd',P')} \<subseteq> NNode \<and> eedge (nd,P) (nd',P')))"
      unfolding NNode_def eedge_def  
      by simp (smt (verit, best) Suc_less_eq Suc_pred diff_is_0_eq' 
         gr_zeroI less_Suc_eq less_imp_le_nat nth_mem)

      with subgr scg obtain nd_P nd_P' where 
      "{nd_P,nd_P'} \<subseteq> NNode \<and> eedge nd_P nd_P'"
      "RR nd_P nd_P' Decr"
      using lim unfolding decreasingHCSC_def Sedge1_def[symmetric] by metis

      then obtain k where k: "k<length nd_Pl - 1" "RR (nd_Pl ! k) (nd_Pl ! Suc k) Decr"
      by (metis Suc_lessE diff_Suc_1 eedge_def) 

      show "\<exists>j\<ge>i. RR (nnds !! j, Ps !! j) (nnds !! Suc j, Ps !! Suc j) Decr"
      apply(rule exI[of _ "j0+k"], safe) 
        subgoal by (simp add: j0(1) trans_le_add1)
        subgoal using k unfolding nd_Pl_def sdrop_snth  
          by (metis Suc_eq_plus1 Suc_mono add_Suc_right add_diff_cancel_right' 
            length_stake less_SucI sdrop_snth snth_szip stake_nth) .
    qed .

  show ?thesis using d_nnds by (simp add: descentIpath_sdrop_any nnds_def)
qed

proposition XSDdescending_implies_InfiniteDescent: 
"XSDdescending \<Longrightarrow> InfiniteDescent"
unfolding XSDdescending_def InfiniteDescent_def 
using decreasingHCSC_imp_descentIpath scsg_limit Node_finite by blast

lemmas Incomplete_Criterion = SDdescending_imp_InfiniteDescent 
                              XSDdescending_implies_InfiniteDescent
end (* context Heighted_Graph *) 


end 
