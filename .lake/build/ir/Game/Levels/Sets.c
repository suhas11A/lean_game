// Lean compiler output
// Module: Game.Levels.Sets
// Imports: Init Game.Levels.Sets.L01_intro Game.Levels.Sets.L02_intervals Game.Levels.Sets.L03_types Game.Levels.Sets.L04_subsets Game.Levels.Sets.L05_equality Game.Levels.Sets.L06_phi Game.Levels.Sets.L07_emptiness Game.Levels.Sets.L08_phi Game.Levels.Sets.L09_power
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
lean_object* initialize_Game_Levels_Sets_L01__intro(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_Sets_L02__intervals(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_Sets_L03__types(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_Sets_L04__subsets(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_Sets_L05__equality(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_Sets_L06__phi(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_Sets_L07__emptiness(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_Sets_L08__phi(uint8_t builtin, lean_object*);
lean_object* initialize_Game_Levels_Sets_L09__power(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Game_Levels_Sets(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L01__intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L02__intervals(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L03__types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L04__subsets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L05__equality(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L06__phi(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L07__emptiness(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L08__phi(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Game_Levels_Sets_L09__power(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
