// Lean compiler output
// Module: Game.Levels.VariablesAndQuantifiers
// Imports: Init Game.Levels.VariablesAndQuantifiers.L01_universalGoal Game.Levels.VariablesAndQuantifiers.L02_universalHypo Game.Levels.VariablesAndQuantifiers.L03_existentialGoal Game.Levels.VariablesAndQuantifiers.L04_existentialHypo Game.Levels.VariablesAndQuantifiers.L05_exercise_1_2_32a Game.Levels.VariablesAndQuantifiers.L06_exercise_1_2_32b Game.Levels.VariablesAndQuantifiers.L07_thm_1_2_33
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_VariablesAndQuantifiers_L01__universalGoal(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_VariablesAndQuantifiers_L02__universalHypo(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_VariablesAndQuantifiers_L03__existentialGoal(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_VariablesAndQuantifiers_L04__existentialHypo(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_VariablesAndQuantifiers_L05__exercise__1__2__32a(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_VariablesAndQuantifiers_L06__exercise__1__2__32b(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_VariablesAndQuantifiers_L07__thm__1__2__33(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Game_Levels_VariablesAndQuantifiers(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_VariablesAndQuantifiers_L01__universalGoal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_VariablesAndQuantifiers_L02__universalHypo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_VariablesAndQuantifiers_L03__existentialGoal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_VariablesAndQuantifiers_L04__existentialHypo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_VariablesAndQuantifiers_L05__exercise__1__2__32a(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_VariablesAndQuantifiers_L06__exercise__1__2__32b(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_VariablesAndQuantifiers_L07__thm__1__2__33(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
