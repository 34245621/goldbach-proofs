// node --test .github/scripts/outside-guard.test.mjs
// The plain-file rule of outside-guard.mjs: one fixture per way a proof file could carry code
// that runs while it compiles (or hide it from a reader), and the honest shapes that must pass.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkGap, checkImports } from './outside-guard.mjs';

test('published tasks accept a community proof with an opted-in support import', () => {
  const gap = {
    id: 'L-goldbach-example',
    file: 'lean/Conjectures/Goldbach/Example.lean',
    module: 'Conjectures.Goldbach.Example',
    statement: 'True',
    imports: ['ResearchSupport.GRH'],
  };
  assert.deepEqual(checkGap({ gaps: [gap] }, g => g.id === gap.id, gap.file),
    { id: gap.id, statement: gap.statement, imports: gap.imports });
  const support = { ...gap, module: 'ResearchSupport.GRH', file: 'lean/ResearchSupport/GRH.lean' };
  assert.throws(() => checkGap({ gaps: [support] }, () => true, support.file), /not the file/);
});

const head = 'import Mathlib\nimport ResearchSupport.Defs\n\n';
const run = (body) => checkImports(new TextEncoder().encode(head + body), ['ResearchSupport.Defs']);
const refused = (name, body, word) => test(`refused: ${name}`, () => {
  assert.throws(() => run(body), (e) => e.message.includes(word), 'not refused, or for another reason');
});
const passes = (name, body) => test(`passes: ${name}`, () => { assert.deepEqual(run(body), ['Mathlib', 'ResearchSupport.Defs']); });
const thm = 'theorem Conjectures.Goldbach.X1 : True := trivial\n';
const by = (tac) => `theorem Conjectures.Goldbach.X1 : True := by\n  ${tac}\n`;

refused('an initialize', `initialize pure ()\n${thm}`, 'initialize');
refused('an indented initialize', `${thm}  initialize pure ()\n`, 'initialize');
refused('run_cmd, indented', `${thm} run_cmd pure ()\n`, 'run_cmd');
refused('#eval', `${thm} #eval 1\n`, '#');
refused('a tactic that runs code', by('run_tac (do return ())'), 'run_tac');
refused('an elaborator, indented', `${thm} elab x : term => pure default\n`, 'elab');
refused('a macro, indented', `${thm} macro x : tactic => y\n`, 'macro');
refused('notation3', `${thm} notation3 x => y\n`, 'notation');
refused('an attribute command', `${thm} attribute [simp] Nat.add_comm\n`, 'attribute');
refused('a generating attribute', `@[to_additive] theorem foo : True := trivial\n${thm}`, '@[');
refused('an option that is not a limit', `set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an indented option that is not a limit', by('set_option debug.skipKernelTC true in\n  trivial'), 'set_option');
refused('a same-line option that is not a limit', `set_option maxHeartbeats 1 in set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an axiom', `${thm} axiom a : False\n`, 'axiom');
refused('sorry', by('sorry'), 'sorry');
refused('sorryAx', 'theorem Conjectures.Goldbach.X1 : False := sorryAx _\n', 'sorry');
refused('lcProof', 'theorem Conjectures.Goldbach.X1 : False := lcProof\n', 'lcProof');
refused('native_decide', by('native_decide'), 'native');
refused('decide +native', by('decide +native'), 'native');
refused('bv_decide', by('bv_decide'), 'bv_decide');
refused('a simproc', `${thm}  simproc foo (x) := y\n`, 'simproc');
refused('open Lean', `open Lean in\n${thm}`, 'Lean');
refused('ofReduceBool', by('exact ofReduceBool x true rfl'), 'ofReduce');
refused('_root_', by('exact _root_.id trivial'), '_root_');
passes('published theorem name containing local_root_pair', thm.replace('L_x_1', 'L_quadratic_primes_local_root_pair'));
refused('include_str', by('exact include_str x'), 'include_str');
refused('polyrith', by('polyrith'), 'polyrith');
refused('a string literal', `private def s : String := "x"\n${thm}`, '"');
refused('a character-literal trick', `${thm}  -- '"'\n`, '"');
refused('a quoted identifier', `private def «a» : Nat := 1\n${thm}`, '«');
refused('code hidden behind a comment trick', `-- a note /- here\n  initialize pure ()\n-- done -/\n${thm}`, 'initialize');
refused('a command after a comment on one line', `/- note -/ initialize pure ()\n${thm}`, 'initialize');
refused('a syntax quotation', by('exact \x60(tactic| trivial)'), '(tactic|');
refused('#check', `#check Nat\n${thm}`, '#check');
refused('#print axioms, indented', `${thm}  #print axioms Nat.add_comm\n`, '#print');
refused('a direction-changing character', `-- ‮\n${thm}`, 'invisible');
refused('no theorem at all', 'def x : Nat := 1\n', 'no theorem');

passes('one theorem', thm);
passes('helpers, definitions, namespaces, a docstring', `namespace Gap\nopen Finset\nvariable {n : ℕ}\n/-- A doc comment. -/\nprivate def f (x : ℕ) : ℕ := x\nprivate lemma l : f 1 = 1 := rfl\nend Gap\n\n${thm}`);
passes('a block comment with indented prose', `/-\n  The idea of the proof,\n  in two lines.\n-/\n${thm}`);
passes('the simp attributes', `@[simp] private theorem a : True := trivial\n@[local simp] private theorem b : True := trivial\n${thm}`);
passes('the four limit options', `set_option maxHeartbeats 400000 in\nset_option maxRecDepth 2000 in\n${thm}`);
passes('an indented limit option inside a proof', by('set_option maxRecDepth 2000 in\n  trivial'));
passes('comment prose at column 0 and a heading (form is not judged)', `/-!\n# A heading\n\nProse that starts in column 0,\nover two lines.\n-/\n${thm}`);
passes('a small enumerated type and an instance', `private inductive Stack | input | output\n  deriving DecidableEq\n\nprivate instance : Inhabited Stack := ⟨.input⟩\n${thm}`);
passes('open scoped, and a cardinality written with a hash', `open scoped BigOperators\ntheorem Conjectures.Goldbach.X1 (s : Finset ℕ) : #s = #s := rfl\n`);
passes('a pair in backticks inside a doc comment', '/-- The coordinates \x60(a, b, c, d)\x60 of the block. -/\n' + thm);
passes('lemma names that contain add_', by('simp only [Nat.add_comm, add_zero]'));

// The closure rule: which listed modules the base step may build, and which are outside-written
// and built only in the locked step. The base tree is a map here; `read` answers null for a file
// that is not a plain file of the base tree.
import { importClosure, headerImports } from './outside-guard.mjs';
const tree = (files) => (m) => (m in files ? new TextEncoder().encode(files[m]) : null);
const proof = (imports, name = 'Conjectures.Goldbach.X2') => `${imports.map((m) => `import ${m}\n`).join('')}\ntheorem ${name} : True := trivial\n`;
const judged = 'Conjectures.Goldbach.X1';
const closure = (listed, files, buildOrder) => importClosure(listed, tree(files), judged, buildOrder);
const closureRefused = (name, listed, files, word) => test(`closure refused: ${name}`, () => {
  assert.throws(() => closure(listed, files), (e) => e.message.includes(word), 'not refused, or for another reason');
});

test('closure: base modules only, as before', () => {
  assert.deepEqual(closure(['ResearchSupport.Sample.A'], { 'ResearchSupport.Sample.A': 'import Mathlib\nimport ResearchSupport.Sample.B\n', 'ResearchSupport.Sample.B': '-- note\nimport ResearchSupport.Defs\n', 'ResearchSupport.Defs': 'import Mathlib\n' }),
    { outside: [], base: ['ResearchSupport.Defs', 'ResearchSupport.Sample.A', 'ResearchSupport.Sample.B'] });
});
test('closure: a listed outside module is never handed to the base step; the base modules it imports are', () => {
  const buildOrder = [];
  const r = closure(['Conjectures.Goldbach.Derived'], {
    'Conjectures.Goldbach.Derived': proof(['Mathlib', 'ResearchSupport.Defs', 'Conjectures.Goldbach.Weights'], 'Conjectures.Goldbach.Derived'),
    'Conjectures.Goldbach.Weights': proof(['Mathlib', 'ResearchSupport.Sample.Weights'], 'Conjectures.Goldbach.Weights'),
    'ResearchSupport.Defs': 'import Mathlib\n', 'ResearchSupport.Sample.Weights': 'import ResearchSupport.Defs\n' }, buildOrder);
  assert.deepEqual(buildOrder, ['Conjectures.Goldbach.Weights', 'Conjectures.Goldbach.Derived']);
  assert.deepEqual(r, { outside: ['Conjectures.Goldbach.Derived', 'Conjectures.Goldbach.Weights'], base: ['ResearchSupport.Defs', 'ResearchSupport.Sample.Weights'] });
});
closureRefused('the judged file itself', [judged], {}, 'the file being judged');
closureRefused('an outside module that imports the judged file', ['Conjectures.Goldbach.X2'], { 'Conjectures.Goldbach.X2': proof([judged]) }, 'the file being judged');
test('closure: a community proof may import a proof from another desk', () => {
  const dependency = 'Conjectures.TwinPrimes.X2';
  const current = 'Conjectures.Goldbach.Sample';
  const order = [];
  importClosure([current], tree({
    [current]: proof([dependency], current),
    [dependency]: proof(['Mathlib'], dependency),
  }), 'Conjectures.Goldbach.Downstream', order);
  assert.deepEqual(order, [dependency, current]);
});
closureRefused('a listed module missing from the base', ['Conjectures.Goldbach.X9'], {}, 'not a plain file of the base tree');
closureRefused('a listed base module missing from the base', ['ResearchSupport.Sample.Nope'], {}, 'not a plain file of the base tree');
closureRefused('a base module that imports an outside module', ['ResearchSupport.Sample.A'], { 'ResearchSupport.Sample.A': 'import ResearchSupport.Sample.B\n', 'ResearchSupport.Sample.B': '/- x -/ import Conjectures.Goldbach.X2\n', 'Conjectures.Goldbach.X2': proof(['Mathlib']) }, 'imports the outside-written');
closureRefused('a base module behind an outside module that imports another outside module', ['Conjectures.Goldbach.X2'], { 'Conjectures.Goldbach.X2': proof(['ResearchSupport.Sample.B']), 'ResearchSupport.Sample.B': 'import Conjectures.Goldbach.X3\n', 'Conjectures.Goldbach.X3': proof([]) }, 'imports the outside-written');
closureRefused('an outside module that runs code when it compiles', ['Conjectures.Goldbach.X2'], { 'Conjectures.Goldbach.X2': `import Mathlib\ninitialize pure ()\n${thm}` }, 'initialize');
closureRefused('an outside module with an import below its header', ['Conjectures.Goldbach.X2'], { 'Conjectures.Goldbach.X2': `import Mathlib\n${thm}/- -/ import ResearchSupport.Sample.B\n` }, 'the word "import"');
closureRefused('an outside module importing something not Mathlib and not the project', ['Conjectures.Goldbach.X2'], { 'Conjectures.Goldbach.X2': proof(['Lean.Elab']) }, 'not allowed');
closureRefused('a module under Conjectures that is not a proof file name', ['Conjectures.Helper'], { 'Conjectures.Helper': proof(['Mathlib']) }, 'not the name of an outside proof file');
test('closure: a cycle between outside modules ends', () => {
  assert.deepEqual(closure(['Conjectures.Goldbach.X2'], { 'Conjectures.Goldbach.X2': proof(['Conjectures.Goldbach.X3']), 'Conjectures.Goldbach.X3': proof(['Conjectures.Goldbach.X2']) }).outside, ['Conjectures.Goldbach.X2', 'Conjectures.Goldbach.X3']);
});

test('header: comments, module, modifiers, quoted names', () => {
  assert.deepEqual(headerImports('/- a /- nested -/ b -/\n-- c\nmodule\npublic import «Conjectures».Goldbach.X2\nmeta import all Mathlib.Tactic\nimport ResearchSupport.Defs -- d\n\ntheorem t : True := trivial\n', 'm'),
    ['Conjectures.Goldbach.X2', 'Mathlib.Tactic', 'ResearchSupport.Defs']);
});
test('header: an import line below the header is refused, never passed over', () => {
  assert.throws(() => headerImports('import Mathlib\ndef x := 1\nimport Conjectures.Goldbach.X2\n', 'm'), /below its header/);
});

// Checker fixtures are excluded from proof dependencies, and outside modules are capped.
import { MAX_OUTSIDE } from './outside-guard.mjs';
closureRefused('a listed fixture module', ['CheckerSuite.Pass'], { 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under an allowed project root');
closureRefused('a base module that imports a fixture module', ['ResearchSupport.Sample.A'], { 'ResearchSupport.Sample.A': 'import CheckerSuite.Pass\n', 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under an allowed project root');
closureRefused('an outside module that imports a fixture module', ['Conjectures.Goldbach.X2'], { 'Conjectures.Goldbach.X2': proof(['CheckerSuite.Pass']), 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under an allowed project root');
const many = (n) => Object.fromEntries(Array.from({ length: n }, (_, k) => [`Conjectures.Goldbach.X${k + 10}`, proof(['Mathlib'], `Conjectures.Goldbach.X${k + 10}`)]));
test(`closure: ${MAX_OUTSIDE} outside modules pass`, () => {
  assert.equal(MAX_OUTSIDE, 16);
  assert.equal(closure(Object.keys(many(MAX_OUTSIDE)), many(MAX_OUTSIDE)).outside.length, MAX_OUTSIDE);
});
closureRefused(`${MAX_OUTSIDE + 1} outside modules listed`, Object.keys(many(MAX_OUTSIDE + 1)), many(MAX_OUTSIDE + 1), `more than ${MAX_OUTSIDE} outside modules`);
test(`closure refused: ${MAX_OUTSIDE + 1} outside modules, one listed and the rest reached through it`, () => {
  const files = many(MAX_OUTSIDE);
  files['Conjectures.Goldbach.X1000'] = proof(Object.keys(many(MAX_OUTSIDE)), 'Conjectures.Goldbach.X1000');
  assert.throws(() => closure(['Conjectures.Goldbach.X1000'], files), /more than 16 outside modules/);
});

test('accepts a 2 MiB proof and refuses one extra byte', () => {
  const limit = 2 * 1024 * 1024;
  const proof = Buffer.alloc(limit + 1, 0x20);
  proof.write(head + thm);
  assert.deepEqual(checkImports(proof.subarray(0, limit), ['ResearchSupport.Defs']), ['Mathlib', 'ResearchSupport.Defs']);
  assert.throws(() => checkImports(proof, ['ResearchSupport.Defs']), /2097152 bytes/);
});

test('allows the GRH source modules for a task that opts in', () => {
  const proof = Buffer.from('import ResearchSupport.GRH\n' + thm);
  assert.deepEqual(checkImports(proof, ['ResearchSupport.GRH']), ['ResearchSupport.GRH']);
  assert.throws(() => checkImports(proof, []), /ResearchSupport\.GRH is not allowed/);
  const internal = Buffer.from('import ResearchSupport.GRHSource.Main\n' + thm);
  assert.deepEqual(checkImports(internal, ['ResearchSupport.GRH']), ['ResearchSupport.GRHSource.Main']);
  assert.throws(() => checkImports(internal, []), /ResearchSupport\.GRHSource\.Main is not allowed/);
});
