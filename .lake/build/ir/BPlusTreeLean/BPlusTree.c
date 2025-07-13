// Lean compiler output
// Module: BPlusTreeLean.BPlusTree
// Imports: Init BPlusTreeLean.Basic
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
LEAN_EXPORT lean_object* l_BPlusTree_getAllLeaves___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex_go(lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNode___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInChildren___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findLeafForKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_delete___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchSteps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findLeafForKey___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInChildren(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_nodeWellFormed_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_nodeWellFormed_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpan_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInChildren___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchInNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_search(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInChildren(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInSubtree(lean_object*, lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
lean_object* l_List_get___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInSubtree___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNodeSafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insert(lean_object*, lean_object*);
lean_object* lean_sorry(uint8_t);
lean_object* l_List_setTR_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf(lean_object*, lean_object*);
static lean_object* l_BPlusTree_insertIntoNode___rarg___closed__1;
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedBPlusNode___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf_insertSorted___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInSubtree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchInNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInChildren___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInChildren(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_search___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInSubtree___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_rangeQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchSteps___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInSubtree___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInChildren___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInChildren(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedBPlusNode___rarg(lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchInLeaf___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_getAllLeaves___rarg(lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInChildren___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNodeSafe___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_search___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_keySpan___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_keySpan(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInSubtree___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpan_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchInLeaf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_BPlusTree_allKeysInSubtree___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_List_get_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpanContained_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInChildren___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInSubtree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInSubtree___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchInNode___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchSteps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpanContained_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf_insertSorted___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findLeafForKey___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNodeSafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex(lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf_insertSorted(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_rangeQuery(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInChildren___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInSubtree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInSubtree___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_delete(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_nodeWellFormed_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInChildren___rarg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInSubtree___rarg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_keySpan___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedBPlusNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_BPlusTree_allKeysInSubtree___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_searchInLeaf___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_getAllLeaves(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_insert___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInSubtree___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedBPlusNode___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instInhabitedBPlusNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instInhabitedBPlusNode___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instInhabitedBPlusNode___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instInhabitedBPlusNode___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_BPlusTree_allKeysInSubtree___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_BPlusTree_allKeysInSubtree___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_mapTR_loop___at_BPlusTree_allKeysInSubtree___spec__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInSubtree___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_BPlusTree_allKeysInSubtree___spec__1___rarg(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_BPlusTree_allKeysInChildren___rarg(x_1, x_7);
x_9 = l_List_appendTR___rarg(x_6, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInSubtree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_allKeysInSubtree___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInChildren___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_BPlusTree_allKeysInSubtree___rarg(x_1, x_4);
x_7 = l_BPlusTree_allKeysInChildren___rarg(x_1, x_5);
x_8 = l_List_appendTR___rarg(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInChildren(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_allKeysInChildren___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInSubtree___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BPlusTree_allKeysInSubtree___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allKeysInChildren___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BPlusTree_allKeysInChildren___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInSubtree___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_free_object(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l_BPlusTree_minKeyInChildren___rarg(x_1, x_2, x_3, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInSubtree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_minKeyInSubtree___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInChildren___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_BPlusTree_minKeyInSubtree___rarg(x_1, x_2, x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_2);
x_10 = l_BPlusTree_minKeyInSubtree___rarg(x_1, x_2, x_3, x_9);
lean_inc(x_2);
x_11 = l_BPlusTree_minKeyInChildren___rarg(x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_inc(x_19);
x_22 = lean_apply_2(x_2, x_19, x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_19);
return x_11;
}
else
{
lean_dec(x_21);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_24);
lean_inc(x_19);
x_25 = lean_apply_2(x_2, x_19, x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_19);
return x_28;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInChildren(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_minKeyInChildren___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInSubtree___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BPlusTree_minKeyInSubtree___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_minKeyInChildren___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BPlusTree_minKeyInChildren___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInSubtree___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_List_getLast_x3f___rarg(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l_BPlusTree_maxKeyInChildren___rarg(x_1, x_2, x_3, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInSubtree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_maxKeyInSubtree___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInChildren___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_BPlusTree_maxKeyInSubtree___rarg(x_1, x_2, x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_2);
x_10 = l_BPlusTree_maxKeyInSubtree___rarg(x_1, x_2, x_3, x_9);
lean_inc(x_2);
x_11 = l_BPlusTree_maxKeyInChildren___rarg(x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_inc(x_19);
x_22 = lean_apply_2(x_2, x_19, x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_21);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_dec(x_19);
return x_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_24);
lean_inc(x_19);
x_25 = lean_apply_2(x_2, x_19, x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInChildren(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_maxKeyInChildren___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInSubtree___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BPlusTree_maxKeyInSubtree___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_maxKeyInChildren___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BPlusTree_maxKeyInChildren___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_4, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter___rarg___boxed), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_minKeyInSubtree_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_nodeWellFormed_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_nodeWellFormed_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_nodeWellFormed_match__1_splitter___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_nodeWellFormed_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_nodeWellFormed_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; 
x_6 = lean_apply_2(x_3, x_5, lean_box(0));
return x_6;
}
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter___rarg___boxed), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_maxKeyInSubtree_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_keySpan___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_BPlusTree_minKeyInSubtree___rarg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_BPlusTree_maxKeyInSubtree___rarg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_keySpan(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_keySpan___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_keySpan___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BPlusTree_keySpan___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpan_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_3(x_4, x_1, x_2, lean_box(0));
return x_5;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_3(x_4, x_1, x_2, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpan_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpan_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpanContained_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_4, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_apply_1(x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_apply_4(x_3, x_10, x_11, x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpanContained_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_BPlusTreeLean_BPlusTree_0__BPlusTree_keySpanContained_match__1_splitter___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_3);
x_8 = lean_apply_2(x_2, x_3, x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_7;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BPlusTree_findChildIndex_go___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_BPlusTree_findChildIndex_go___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_BPlusTree_findChildIndex_go___rarg(x_1, x_2, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BPlusTree_findChildIndex___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findChildIndex___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BPlusTree_findChildIndex___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findLeafForKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_2);
x_10 = l_BPlusTree_findChildIndex_go___rarg(x_1, x_2, x_5, x_9, x_7);
x_11 = l_List_lengthTRAux___rarg(x_8, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_dec_le(x_10, x_13);
x_15 = l_instInhabitedBPlusNode___rarg(x_3);
if (x_14 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = l_List_get_x21___rarg(x_15, x_8, x_13);
lean_dec(x_8);
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_13);
x_18 = l_List_get_x21___rarg(x_15, x_8, x_10);
lean_dec(x_8);
x_4 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findLeafForKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_findLeafForKey___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_findLeafForKey___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_BPlusTree_findLeafForKey___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchInLeaf___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchInLeaf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_BPlusTree_searchInLeaf___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_List_find_x3f___rarg(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchInLeaf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_searchInLeaf___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchInNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_6);
x_7 = l_BPlusTree_findLeafForKey___rarg(x_1, x_2, x_4, x_5, x_6);
x_8 = l_BPlusTree_searchInLeaf___rarg(x_3, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchInNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_searchInNode___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchInNode___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_BPlusTree_searchInNode___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_search___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_BPlusTree_searchInNode___rarg(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_search(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_search___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_search___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_BPlusTree_search___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf_insertSorted___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_4);
x_13 = lean_apply_2(x_2, x_4, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = l_BPlusTree_insertIntoLeaf_insertSorted___rarg(x_1, x_2, x_3, x_4, x_5, x_11);
lean_ctor_set(x_6, 1, x_15);
return x_6;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_16 = lean_apply_2(x_3, x_4, x_12);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_inc(x_2);
lean_inc(x_21);
lean_inc(x_4);
x_22 = lean_apply_2(x_2, x_4, x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
x_24 = l_BPlusTree_insertIntoLeaf_insertSorted___rarg(x_1, x_2, x_3, x_4, x_5, x_20);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_2);
x_26 = lean_apply_2(x_3, x_4, x_21);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_20);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf_insertSorted(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_insertIntoLeaf_insertSorted___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf_insertSorted___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_BPlusTree_insertIntoLeaf_insertSorted___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_BPlusTree_insertIntoLeaf_insertSorted___rarg(x_1, x_2, x_3, x_5, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_insertIntoLeaf___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoLeaf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_BPlusTree_insertIntoLeaf___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_BPlusTree_insertIntoNode___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = l_BPlusTree_insertIntoLeaf___rarg(x_2, x_4, x_5, x_11, x_8, x_9);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_BPlusTree_insertIntoLeaf___rarg(x_2, x_4, x_5, x_13, x_8, x_9);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
lean_inc(x_8);
lean_inc(x_3);
x_20 = l_BPlusTree_findChildIndex_go___rarg(x_1, x_3, x_8, x_19, x_17);
x_21 = l_List_lengthTRAux___rarg(x_18, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = lean_nat_dec_le(x_20, x_23);
x_25 = l_instInhabitedBPlusNode___rarg(x_6);
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_inc(x_23);
x_26 = l_List_get_x21___rarg(x_25, x_18, x_23);
x_27 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
x_28 = l_BPlusTree_insertIntoNode___rarg___closed__1;
lean_inc(x_18);
x_29 = l_List_setTR_go___rarg(x_18, x_27, x_18, x_23, x_28);
lean_dec(x_18);
lean_ctor_set(x_7, 1, x_29);
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
lean_inc(x_20);
x_30 = l_List_get_x21___rarg(x_25, x_18, x_20);
x_31 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_30, x_8, x_9);
x_32 = l_BPlusTree_insertIntoNode___rarg___closed__1;
lean_inc(x_18);
x_33 = l_List_setTR_go___rarg(x_18, x_31, x_18, x_20, x_32);
lean_dec(x_18);
lean_ctor_set(x_7, 1, x_33);
return x_7;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_unsigned_to_nat(0u);
lean_inc(x_34);
lean_inc(x_8);
lean_inc(x_3);
x_37 = l_BPlusTree_findChildIndex_go___rarg(x_1, x_3, x_8, x_36, x_34);
x_38 = l_List_lengthTRAux___rarg(x_35, x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = lean_nat_dec_le(x_37, x_40);
x_42 = l_instInhabitedBPlusNode___rarg(x_6);
if (x_41 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_inc(x_40);
x_43 = l_List_get_x21___rarg(x_42, x_35, x_40);
x_44 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_43, x_8, x_9);
x_45 = l_BPlusTree_insertIntoNode___rarg___closed__1;
lean_inc(x_35);
x_46 = l_List_setTR_go___rarg(x_35, x_44, x_35, x_40, x_45);
lean_dec(x_35);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_40);
lean_inc(x_37);
x_48 = l_List_get_x21___rarg(x_42, x_35, x_37);
x_49 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_48, x_8, x_9);
x_50 = l_BPlusTree_insertIntoNode___rarg___closed__1;
lean_inc(x_35);
x_51 = l_List_setTR_go___rarg(x_35, x_49, x_35, x_37, x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_34);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_insertIntoNode___rarg___boxed), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNode___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNodeSafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = l_BPlusTree_insertIntoLeaf___rarg(x_2, x_4, x_5, x_14, x_11, x_12);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_BPlusTree_insertIntoLeaf___rarg(x_2, x_4, x_5, x_16, x_11, x_12);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_20);
lean_inc(x_11);
lean_inc(x_3);
x_23 = l_BPlusTree_findChildIndex_go___rarg(x_1, x_3, x_11, x_22, x_20);
lean_inc(x_23);
x_24 = l_List_get___rarg(x_21, x_23);
x_25 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_8, x_24, x_11, x_12);
x_26 = l_BPlusTree_insertIntoNode___rarg___closed__1;
lean_inc(x_21);
x_27 = l_List_setTR_go___rarg(x_21, x_25, x_21, x_23, x_26);
lean_dec(x_21);
lean_ctor_set(x_9, 1, x_27);
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_28);
lean_inc(x_11);
lean_inc(x_3);
x_31 = l_BPlusTree_findChildIndex_go___rarg(x_1, x_3, x_11, x_30, x_28);
lean_inc(x_31);
x_32 = l_List_get___rarg(x_29, x_31);
x_33 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_8, x_32, x_11, x_12);
x_34 = l_BPlusTree_insertIntoNode___rarg___closed__1;
lean_inc(x_29);
x_35 = l_List_setTR_go___rarg(x_29, x_33, x_29, x_31, x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNodeSafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_insertIntoNodeSafe___rarg___boxed), 12, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insertIntoNodeSafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_BPlusTree_insertIntoNodeSafe___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l_BPlusTree_insertIntoNode___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_insert___rarg___boxed), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_insert___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_BPlusTree_insert___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_delete(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = lean_sorry(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_delete___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_BPlusTree_delete(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_rangeQuery(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = lean_sorry(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_rangeQuery___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_BPlusTree_rangeQuery(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInSubtree___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_BPlusTree_allEntriesInChildren___rarg(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInSubtree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_allEntriesInSubtree___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInChildren___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_BPlusTree_allEntriesInSubtree___rarg(x_1, x_4);
x_7 = l_BPlusTree_allEntriesInChildren___rarg(x_1, x_5);
x_8 = l_List_appendTR___rarg(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInChildren(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BPlusTree_allEntriesInChildren___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInSubtree___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BPlusTree_allEntriesInSubtree___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_allEntriesInChildren___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BPlusTree_allEntriesInChildren___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_getAllLeaves___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 0;
x_3 = lean_sorry(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_getAllLeaves(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_BPlusTree_getAllLeaves___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_getAllLeaves___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BPlusTree_getAllLeaves(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchSteps___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 0;
x_4 = lean_sorry(x_3);
x_5 = lean_apply_2(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchSteps(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_BPlusTree_searchSteps___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BPlusTree_searchSteps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BPlusTree_searchSteps(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_BPlusTreeLean_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_BPlusTreeLean_BPlusTree(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BPlusTreeLean_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_BPlusTree_insertIntoNode___rarg___closed__1 = _init_l_BPlusTree_insertIntoNode___rarg___closed__1();
lean_mark_persistent(l_BPlusTree_insertIntoNode___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
