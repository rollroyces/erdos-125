// Lean compiler output
// Module: Erdos125
// Imports: public import Init public meta import Init public import Mathlib
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_List_range(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lp_mathlib_List_mapTR_loop___at___00List_ranges_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lp_mathlib_List_eraseDups___at___00Mathlib_Tactic_Linarith_runLinarith_spec__5(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_inA_helper(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_inA_helper___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_inA(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_inA___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_List_foldl___at___00Erdos125_countA_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_countA(lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_inB_helper(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_inB_helper___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_inB(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_inB___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_List_foldl___at___00Erdos125_countB_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_countB(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Erdos125_countAB_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Erdos125_countAB_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_erdos125_Erdos125_countAB___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_erdos125_Erdos125_countAB___closed__0 = (const lean_object*)&lp_erdos125_Erdos125_countAB___closed__0_value;
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_countAB(lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_List_all___at___00Erdos125_bijection__holds_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_List_all___at___00Erdos125_bijection__holds_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_bijection__holds(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_bijection__holds___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_List_all___at___00Erdos125_third__range__false_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_List_all___at___00Erdos125_third__range__false_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_third__range__false(lean_object*);
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_third__range__false___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_inA_helper(lean_object* v_m_1_){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_nat_dec_eq(v_m_1_, v___x_2_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_unsigned_to_nat(3u);
v___x_6_ = lean_nat_mod(v_m_1_, v___x_5_);
v___x_7_ = lean_nat_dec_lt(v___x_4_, v___x_6_);
lean_dec(v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_nat_div(v_m_1_, v___x_5_);
lean_dec(v_m_1_);
v_m_1_ = v___x_8_;
goto _start;
}
else
{
lean_dec(v_m_1_);
return v___x_3_;
}
}
else
{
lean_dec(v_m_1_);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_inA_helper___boxed(lean_object* v_m_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_erdos125_Erdos125_inA_helper(v_m_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_inA(lean_object* v_n_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lp_erdos125_Erdos125_inA_helper(v_n_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_inA___boxed(lean_object* v_n_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = lp_erdos125_Erdos125_inA(v_n_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_List_foldl___at___00Erdos125_countA_spec__0(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
return v_x_18_;
}
else
{
lean_object* v_head_20_; lean_object* v_tail_21_; uint8_t v___x_22_; 
v_head_20_ = lean_ctor_get(v_x_19_, 0);
lean_inc(v_head_20_);
v_tail_21_ = lean_ctor_get(v_x_19_, 1);
lean_inc(v_tail_21_);
lean_dec_ref_known(v_x_19_, 2);
v___x_22_ = lp_erdos125_Erdos125_inA_helper(v_head_20_);
if (v___x_22_ == 0)
{
v_x_19_ = v_tail_21_;
goto _start;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_add(v_x_18_, v___x_24_);
lean_dec(v_x_18_);
v_x_18_ = v___x_25_;
v_x_19_ = v_tail_21_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_countA(lean_object* v_N_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = l_List_range(v_N_27_);
v___x_30_ = lp_erdos125_List_foldl___at___00Erdos125_countA_spec__0(v___x_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_inB_helper(lean_object* v_m_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_nat_dec_eq(v_m_31_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_34_ = lean_unsigned_to_nat(1u);
v___x_35_ = lean_unsigned_to_nat(4u);
v___x_36_ = lean_nat_mod(v_m_31_, v___x_35_);
v___x_37_ = lean_nat_dec_lt(v___x_34_, v___x_36_);
lean_dec(v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(2u);
v___x_39_ = lean_nat_shiftr(v_m_31_, v___x_38_);
lean_dec(v_m_31_);
v_m_31_ = v___x_39_;
goto _start;
}
else
{
lean_dec(v_m_31_);
return v___x_33_;
}
}
else
{
lean_dec(v_m_31_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_inB_helper___boxed(lean_object* v_m_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = lp_erdos125_Erdos125_inB_helper(v_m_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_inB(lean_object* v_n_44_){
_start:
{
uint8_t v___x_45_; 
v___x_45_ = lp_erdos125_Erdos125_inB_helper(v_n_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_inB___boxed(lean_object* v_n_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = lp_erdos125_Erdos125_inB(v_n_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_List_foldl___at___00Erdos125_countB_spec__0(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
return v_x_49_;
}
else
{
lean_object* v_head_51_; lean_object* v_tail_52_; uint8_t v___x_53_; 
v_head_51_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_head_51_);
v_tail_52_ = lean_ctor_get(v_x_50_, 1);
lean_inc(v_tail_52_);
lean_dec_ref_known(v_x_50_, 2);
v___x_53_ = lp_erdos125_Erdos125_inB_helper(v_head_51_);
if (v___x_53_ == 0)
{
v_x_50_ = v_tail_52_;
goto _start;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_add(v_x_49_, v___x_55_);
lean_dec(v_x_49_);
v_x_49_ = v___x_56_;
v_x_50_ = v_tail_52_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_countB(lean_object* v_N_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = l_List_range(v_N_58_);
v___x_61_ = lp_erdos125_List_foldl___at___00Erdos125_countB_spec__0(v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__0(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
if (lean_obj_tag(v_a_62_) == 0)
{
lean_object* v___x_64_; 
v___x_64_ = l_List_reverse___redArg(v_a_63_);
return v___x_64_;
}
else
{
lean_object* v_head_65_; lean_object* v_tail_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_76_; 
v_head_65_ = lean_ctor_get(v_a_62_, 0);
v_tail_66_ = lean_ctor_get(v_a_62_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_a_62_);
if (v_isSharedCheck_76_ == 0)
{
v___x_68_ = v_a_62_;
v_isShared_69_ = v_isSharedCheck_76_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_tail_66_);
lean_inc(v_head_65_);
lean_dec(v_a_62_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_76_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
uint8_t v___x_70_; 
lean_inc(v_head_65_);
v___x_70_ = lp_erdos125_Erdos125_inA_helper(v_head_65_);
if (v___x_70_ == 0)
{
lean_del_object(v___x_68_);
lean_dec(v_head_65_);
v_a_62_ = v_tail_66_;
goto _start;
}
else
{
lean_object* v___x_73_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v_a_63_);
v___x_73_ = v___x_68_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_head_65_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_a_63_);
v___x_73_ = v_reuseFailAlloc_75_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
v_a_62_ = v_tail_66_;
v_a_63_ = v___x_73_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__3(lean_object* v_N_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
if (lean_obj_tag(v_a_78_) == 0)
{
lean_object* v___x_80_; 
v___x_80_ = l_List_reverse___redArg(v_a_79_);
return v___x_80_;
}
else
{
lean_object* v_head_81_; lean_object* v_tail_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_92_; 
v_head_81_ = lean_ctor_get(v_a_78_, 0);
v_tail_82_ = lean_ctor_get(v_a_78_, 1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_a_78_);
if (v_isSharedCheck_92_ == 0)
{
v___x_84_ = v_a_78_;
v_isShared_85_ = v_isSharedCheck_92_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_tail_82_);
lean_inc(v_head_81_);
lean_dec(v_a_78_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_92_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
uint8_t v___x_86_; 
v___x_86_ = lean_nat_dec_lt(v_head_81_, v_N_77_);
if (v___x_86_ == 0)
{
lean_del_object(v___x_84_);
lean_dec(v_head_81_);
v_a_78_ = v_tail_82_;
goto _start;
}
else
{
lean_object* v___x_89_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v_a_79_);
v___x_89_ = v___x_84_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_head_81_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_a_79_);
v___x_89_ = v_reuseFailAlloc_91_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v_a_78_ = v_tail_82_;
v_a_79_ = v___x_89_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__3___boxed(lean_object* v_N_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__3(v_N_93_, v_a_94_, v_a_95_);
lean_dec(v_N_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__1(lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
if (lean_obj_tag(v_a_97_) == 0)
{
lean_object* v___x_99_; 
v___x_99_ = l_List_reverse___redArg(v_a_98_);
return v___x_99_;
}
else
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_111_; 
v_head_100_ = lean_ctor_get(v_a_97_, 0);
v_tail_101_ = lean_ctor_get(v_a_97_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_a_97_);
if (v_isSharedCheck_111_ == 0)
{
v___x_103_ = v_a_97_;
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_tail_101_);
lean_inc(v_head_100_);
lean_dec(v_a_97_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
uint8_t v___x_105_; 
lean_inc(v_head_100_);
v___x_105_ = lp_erdos125_Erdos125_inB_helper(v_head_100_);
if (v___x_105_ == 0)
{
lean_del_object(v___x_103_);
lean_dec(v_head_100_);
v_a_97_ = v_tail_101_;
goto _start;
}
else
{
lean_object* v___x_108_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_a_98_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_head_100_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_a_98_);
v___x_108_ = v_reuseFailAlloc_110_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
v_a_97_ = v_tail_101_;
v_a_98_ = v___x_108_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_erdos125___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Erdos125_countAB_spec__2(lean_object* v_B_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
if (lean_obj_tag(v_a_113_) == 0)
{
lean_object* v___x_115_; 
lean_dec(v_B_112_);
v___x_115_ = lean_array_to_list(v_a_114_);
return v___x_115_;
}
else
{
lean_object* v_head_116_; lean_object* v_tail_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_head_116_ = lean_ctor_get(v_a_113_, 0);
v_tail_117_ = lean_ctor_get(v_a_113_, 1);
v___x_118_ = lean_box(0);
lean_inc(v_B_112_);
v___x_119_ = lp_mathlib_List_mapTR_loop___at___00List_ranges_spec__0(v_head_116_, v_B_112_, v___x_118_);
v___x_120_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_114_, v___x_119_);
v_a_113_ = v_tail_117_;
v_a_114_ = v___x_120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_erdos125___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Erdos125_countAB_spec__2___boxed(lean_object* v_B_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = lp_erdos125___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Erdos125_countAB_spec__2(v_B_122_, v_a_123_, v_a_124_);
lean_dec(v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_countAB(lean_object* v_N_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_A_131_; lean_object* v_B_132_; lean_object* v___x_133_; lean_object* v_sums_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_inc(v_N_128_);
v___x_129_ = l_List_range(v_N_128_);
v___x_130_ = lean_box(0);
lean_inc(v___x_129_);
v_A_131_ = lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__0(v___x_129_, v___x_130_);
v_B_132_ = lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__1(v___x_129_, v___x_130_);
v___x_133_ = ((lean_object*)(lp_erdos125_Erdos125_countAB___closed__0));
v_sums_134_ = lp_erdos125___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Erdos125_countAB_spec__2(v_B_132_, v_A_131_, v___x_133_);
lean_dec(v_A_131_);
v___x_135_ = lp_erdos125_List_filterTR_loop___at___00Erdos125_countAB_spec__3(v_N_128_, v_sums_134_, v___x_130_);
lean_dec(v_N_128_);
v___x_136_ = lp_mathlib_List_eraseDups___at___00Mathlib_Tactic_Linarith_runLinarith_spec__5(v___x_135_);
v___x_137_ = l_List_lengthTR___redArg(v___x_136_);
lean_dec(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT uint8_t lp_erdos125_List_all___at___00Erdos125_bijection__holds_spec__0(lean_object* v_N_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
else
{
lean_object* v_head_141_; lean_object* v_tail_142_; uint8_t v___y_144_; lean_object* v_n_146_; uint8_t v___x_147_; uint8_t v___x_148_; 
v_head_141_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_head_141_);
v_tail_142_ = lean_ctor_get(v_x_139_, 1);
lean_inc(v_tail_142_);
lean_dec_ref_known(v_x_139_, 2);
v_n_146_ = lean_nat_add(v_N_138_, v_head_141_);
v___x_147_ = lp_erdos125_Erdos125_inA_helper(v_n_146_);
v___x_148_ = lp_erdos125_Erdos125_inA_helper(v_head_141_);
if (v___x_147_ == 0)
{
if (v___x_148_ == 0)
{
v_x_139_ = v_tail_142_;
goto _start;
}
else
{
v___y_144_ = v___x_147_;
goto v___jp_143_;
}
}
else
{
v___y_144_ = v___x_148_;
goto v___jp_143_;
}
v___jp_143_:
{
if (v___y_144_ == 0)
{
lean_dec(v_tail_142_);
return v___y_144_;
}
else
{
v_x_139_ = v_tail_142_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_erdos125_List_all___at___00Erdos125_bijection__holds_spec__0___boxed(lean_object* v_N_150_, lean_object* v_x_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = lp_erdos125_List_all___at___00Erdos125_bijection__holds_spec__0(v_N_150_, v_x_151_);
lean_dec(v_N_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_bijection__holds(lean_object* v_N_154_){
_start:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
lean_inc(v_N_154_);
v___x_155_ = l_List_range(v_N_154_);
v___x_156_ = lp_erdos125_List_all___at___00Erdos125_bijection__holds_spec__0(v_N_154_, v___x_155_);
lean_dec(v_N_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_bijection__holds___boxed(lean_object* v_N_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = lp_erdos125_Erdos125_bijection__holds(v_N_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT uint8_t lp_erdos125_List_all___at___00Erdos125_third__range__false_spec__0(lean_object* v_N_160_, lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 1;
return v___x_162_;
}
else
{
lean_object* v_head_163_; lean_object* v_tail_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_n_167_; uint8_t v___x_168_; 
v_head_163_ = lean_ctor_get(v_x_161_, 0);
v_tail_164_ = lean_ctor_get(v_x_161_, 1);
v___x_165_ = lean_unsigned_to_nat(2u);
v___x_166_ = lean_nat_mul(v___x_165_, v_N_160_);
v_n_167_ = lean_nat_add(v___x_166_, v_head_163_);
lean_dec(v___x_166_);
v___x_168_ = lp_erdos125_Erdos125_inA_helper(v_n_167_);
if (v___x_168_ == 0)
{
v_x_161_ = v_tail_164_;
goto _start;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* lp_erdos125_List_all___at___00Erdos125_third__range__false_spec__0___boxed(lean_object* v_N_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = lp_erdos125_List_all___at___00Erdos125_third__range__false_spec__0(v_N_171_, v_x_172_);
lean_dec(v_x_172_);
lean_dec(v_N_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t lp_erdos125_Erdos125_third__range__false(lean_object* v_N_175_){
_start:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
lean_inc(v_N_175_);
v___x_176_ = l_List_range(v_N_175_);
v___x_177_ = lp_erdos125_List_all___at___00Erdos125_third__range__false_spec__0(v_N_175_, v___x_176_);
lean_dec(v___x_176_);
lean_dec(v_N_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_erdos125_Erdos125_third__range__false___boxed(lean_object* v_N_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = lp_erdos125_Erdos125_third__range__false(v_N_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_erdos125_Erdos125(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
