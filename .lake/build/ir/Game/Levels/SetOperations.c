// Lean compiler output
// Module: Game.Levels.SetOperations
// Imports: Init Game.Levels.SetOperations.L01_intro Game.Levels.SetOperations.L02_inter Game.Levels.SetOperations.L03_sub Game.Levels.SetOperations.L04_distribute Game.Levels.SetOperations.L05_diff Game.Levels.SetOperations.L06_diff Game.Levels.SetOperations.L07_cartesion
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
lean_object* initialize_Game_Levels_SetOperations_L01__intro(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_SetOperations_L02__inter(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_SetOperations_L03__sub(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_SetOperations_L04__distribute(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_SetOperations_L05__diff(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_SetOperations_L06__diff(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_SetOperations_L07__cartesion(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Game_Levels_SetOperations(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_SetOperations_L01__intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_SetOperations_L02__inter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_SetOperations_L03__sub(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_SetOperations_L04__distribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_SetOperations_L05__diff(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_SetOperations_L06__diff(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_SetOperations_L07__cartesion(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
