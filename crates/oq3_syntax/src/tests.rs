// Copyright contributors to the openqasm-parser project
// SPDX-License-Identifier: Apache-2.0

use crate::ast::HasTextName;
use crate::ast::{self, HasArgList, HasName}; // for methods: text(), string()
                                             //use oq3_syntax::ast;
                                             // use std::{
                                             //    fs,
                                             //    path::{Path, PathBuf},
                                             // };
                                             // use ast::HasName;
                                             //use expect_test::expect_file;
                                             // use rayon::prelude::*;
                                             // Adds complication from rust-analyzer
                                             // use test_utils::{bench, bench_fixture, project_root};
                                             //use crate::{ast, AstNode, SourceFile, SyntaxError};
use crate::{AstNode, SourceFile};

// fn collect_stmts(code: &str) -> (usize, Vec<ast::Stmt>){
//     let parse = SourceFile::parse(code);
//     let file : SourceFile = parse.tree();
//     let stmts = file.statements().collect::<Vec<_>>();
//     return (parse.errors.len(), stmts)
// }

#[test]
fn parse_measure_1_test() {
    let code = r##"
measure q;
    "##;
    let parse = SourceFile::parse(code);
    assert!(parse.ok().is_ok());
}

#[test]
fn parse_measure_err1_test() {
    let code = r##"
measure;
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 1);
}

#[test]
fn parse_barrier_1_test() {
    let code = r##"
barrier q;
    "##;
    let parse = SourceFile::parse(code);
    assert!(parse.ok().is_ok());
}

#[test]
fn parse_barrier_2_test() {
    let code = r##"
barrier;
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_gate_def_test() {
    let code = r##"
gate h q {
   U(π/2, 0, π, q);
   gphase(-π/4);
}
    "##;
    let parse = SourceFile::parse(code);
    assert!(parse.ok().is_ok());
}

#[test]
fn parse_gate_call_test() {
    let code = r##"
h q;
    "##;
    let parse = SourceFile::parse(code);
    assert!(parse.ok().is_ok());
}

#[test]
fn parse_gate_call_err1_test() {
    let code = r##"
h q; ()
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 1);
}

#[test]
fn parse_let_test() {
    let code = r##"
def myfunc() {
   let x = q;
}
    "##;
    let parse = SourceFile::parse(code);
    assert!(parse.ok().is_ok());
}

#[test]
fn parse_qasm_test() {
    let code = r##"
gate chpase(x) a, b {
 CX a, b;
}
    "##;

    let parse = SourceFile::parse(code);
    assert!(parse.ok().is_ok());
}

#[test]
fn parse_qasm_err1_test() {
    let code = r##"
gate chpase() a, b {
 CX a, b;
}
    "##;

    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 1);
}

#[test]
fn parse_qasm_err2_test() {
    let code = r##"
gate chpase(x) a b {
 CX a, b;
}
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 1);
}

#[test]
fn parse_qasm_err3_test() {
    let code = r##"
gate chpase() a b {
 CX a, b;
}
    "##;

    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 2);
}

#[test]
fn parse_qasm_defcal_2_test() {
    let code = r##"
defcal xmeasure(int a, int b) q, p {
   1 + 1;
}
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_qasm_defcal_err2_test() {
    let code = r##"
defcal xmeasure(int a, b) q, p -> bit {
   1 + 1;
}
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 1);
}

#[test]
fn parse_qasm_defcal_err1_test() {
    let code = r##"
defcal xmeasure(int a, int b) q, p -> {
   1 + 1;
}
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 1);
}

#[test]
fn parse_qasm_defcal_test() {
    let code = r##"
defcal xmeasure(int a, int b) q, p -> bit {
   1 + 1;
}
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_qasm_def_test() {
    let code = r##"
def xmeasure(int q, int q2) -> bit {
    h q;
    return measure q;
}
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_qasm_def2_test() {
    let code = r##"
def xmeasure(q) -> bit {
    h q;
    return measure q;
}
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 1);
}

#[test]
fn with_details_test() {
    use crate::ast;
    use ast::HasName;

    let code = r##"
defcal xmeasure(int a, int b) q, p -> bit {
   1 + 1;
}
   "##;

    // Get tree and list of errors
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);

    // Get just the tree, as a SyntaxNode
    let file: SourceFile = parse.tree();

    let mut defcal = None;
    for stmt in file.statements() {
        if let ast::Stmt::DefCal(f) = stmt {
            defcal = Some(f)
        }
    }
    let defcal: ast::DefCal = defcal.unwrap();
    let name: Option<ast::Name> = defcal.name();
    let name = name.unwrap();
    assert_eq!(name.text(), "xmeasure");
}

#[test]
fn variable_declaration() {
    let code = r##"
int x;
   "##;
    let parse = SourceFile::parse(code);
    assert!(parse.errors().is_empty());
    let mut stmts = parse.tree().statements();
    let decl = match stmts.next() {
        Some(ast::Stmt::ClassicalDeclarationStatement(s)) => s,
        _ => unreachable!(),
    };
    let scalar_type = decl.scalar_type().unwrap();
    assert_eq!(scalar_type.kind(), ast::ScalarTypeKind::Int);
    assert!(scalar_type.designator().is_none());
}

#[test]
fn parse_cast_expr_test_1() {
    let code = r##"
int(x);
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_cast_expr_test_2() {
    let code = r##"
uint(x);
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_cast_expr_test_3() {
    let code = r##"
float(x);
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_cast_expr_test_4() {
    let code = r##"
int[32](x);
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_cast_expr_test_5() {
    let code = r##"
z + int(x);
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_cast_expr_test_6() {
    let code = r##"
int(x) + z;
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

// Issue #208 and associated PR
#[test]
fn parse_cast_expr_test_7() {
    let code = r##"
z + int[32](x);
    "##;
    let parse = SourceFile::parse(code);
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_extern_check() {
    let code = r##"
extern add(int a, int b) -> int;
extern version() -> int;
extern foo();
extern bar(int x);
bar(10);
"##;
    let parse = SourceFile::parse(code);

    // We expect no errors (zero errors) while parsing extern statements.
    assert_eq!(parse.errors.len(), 0);
}

#[test]
fn parse_extern_check_call() {
    let code = r##"
extern bar(int x);
bar(10);
"##;
    let parse = SourceFile::parse(code);

    // We expect no errors (zero errors) while parsing extern statements.
    assert_eq!(parse.errors.len(), 0);

    let file: SourceFile = parse.tree();

    //let mut ext = None;
    let mut statements = file.statements();
    //assert_eq!(statements.count(),2);

    let ext = match statements.next().as_ref().expect("no extern stmt found") {
        ast::Stmt::Extern(e) => e.clone(),
        _ => panic!("first statement is not extern"),
    };
    assert_eq!(ext.name().expect("no name of extern").text(), "bar");
    let call = match statements.next().expect("no call stmt found") {
        ast::Stmt::ExprStmt(c) => c
            .expr()
            .and_then(|e| match e {
                ast::Expr::CallExpr(c) => Some(c),
                _ => None,
            })
            .expect("should be call expr"),
        _ => panic!("second statement is not call"),
    };

    let name = call.expr().expect("call has no expr");
    assert_eq!(name.syntax().text(), "bar");
    let expr_list = call
        .arg_list()
        .expect("call has no arg_list")
        .expression_list()
        .expect("arg_list has no expression_list");
    assert_eq!(expr_list.exprs().clone().count(), 1);
    let value = expr_list.exprs().next().expect("no expr in expr_list");
    let num = match value {
        ast::Expr::Literal(n) => n,
        _ => panic!("expr is not int literal"),
    };
    assert_eq!((num.syntax().text()), "10");
}

#[test]
fn parse_extern_complete_test() {
    let code = r##"
extern foo(int a, float[32] b) -> bit;
    "##;
    let parse = SourceFile::parse(code);
    assert!(
        parse.clone().ok().is_ok(),
        "unexpected errors: {:?}",
        parse.errors
    );

    // Inspect the AST
    use crate::ast;
    use ast::HasName;
    let file: SourceFile = parse.tree();

    let mut ext = None;
    for stmt in file.statements() {
        if let ast::Stmt::Extern(e) = stmt {
            ext = Some(e);
        }
    }
    let ext = ext.expect("no extern stmt found");

    // name
    let name = ext.name().expect("extern has no name");
    assert_eq!(name.text(), "foo");

    // params: (int a, float[32] b)
    let tplist = ext
        .typed_param_list()
        .expect("extern has no typed_param_list");
    let mut params = tplist.typed_params();

    let p1 = params.next().expect("missing param 1");
    assert_eq!(p1.name().unwrap().text(), "a");
    assert_eq!(p1.scalar_type().unwrap().kind(), ast::ScalarTypeKind::Int);

    let p2 = params.next().expect("missing param 2");
    assert_eq!(p2.name().unwrap().text(), "b");
    assert_eq!(p2.scalar_type().unwrap().kind(), ast::ScalarTypeKind::Float);

    // designator [32]
    let desg = p2.scalar_type().unwrap().designator().unwrap();
    // the designator is an Expr; just ensure it exists
    assert!(desg.expr().is_some());

    assert!(params.next().is_none(), "unexpected extra params");

    // return type: -> bit
    let ret_sig = ext
        .return_signature()
        .expect("extern missing return_signature");
    let ret_ty = ret_sig.scalar_type().expect("extern missing scalar_type");
    assert_eq!(ret_ty.kind(), ast::ScalarTypeKind::Bit);
}
