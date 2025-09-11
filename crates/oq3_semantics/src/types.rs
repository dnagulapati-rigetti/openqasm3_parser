// Copyright contributors to the openqasm-parser project
// SPDX-License-Identifier: Apache-2.0

// Defines the data structures representing the types used to annotate types of expressions in
// the typed ASG.
// This file should include all code that manipulates the types. In particular type promotion
// is implemented here. Casting is not implemented here because it involves not only the types,
// but the typed AST as well.

// Tuple fields (Option<u32>, bool) are (width, is_const).
// width == None, means no width specified. Spec sometimes says "machine" int, etc.
//
// Problem: We will later want to extend this to array types.
// Arrays up to seven dimensions are allowed. But specifying the
// type and width and dimensions as follows greatly increases the size of `enum Type`:
// ArrayInt(u32, (d1,...,d7))
//
// Widths are currently Option<u32>. This may not be the most efficient or performant way
// to handle absence of widths. For example Int(u32,bool) and IntM(bool) for "machine" int.
// But the current implementation is faster and less complex to code.

use boolenum::BoolEnum;

#[derive(BoolEnum, Clone, Debug, PartialEq, Eq, Hash)]
pub enum IsConst {
    True,
    False,
}

// I think semantics of these should be cleared up before implementing
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum IOType {
    Input,
    Output,
    Neither,
}

// From the OQ3 Spec:
// The supported [base types for arrays] include various sizes of ``bit``,
// ``int``, ``uint``, ``float``, ``complex``, and ``angle``, as well as
// ``bool`` and ``duration``

/// Bit width of primitive classical types
type Width = Option<u32>;

#[allow(dead_code)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    // Scalar types
    Bit(IsConst),
    Qubit,
    HardwareQubit,

    Int(Width, IsConst),
    UInt(Width, IsConst),
    Float(Width, IsConst),
    Angle(Width, IsConst),
    Complex(Width, IsConst), // width is for one component.
    Bool(IsConst),           // bool field is is_const
    Duration(IsConst),
    Stretch(IsConst),

    // Arrays (concrete variants)
    BitArray(ArrayDims, IsConst),
    QubitArray(ArrayDims),
    IntArray(ArrayDims, Width, IsConst),
    UIntArray(ArrayDims, Width, IsConst),
    FloatArray(ArrayDims, Width, IsConst),
    AngleArray(ArrayDims, Width, IsConst),
    ComplexArray(ArrayDims, Width, IsConst),
    BoolArray(ArrayDims, IsConst),
    DurationArray(ArrayDims, IsConst),


    // Other
    Gate(usize, usize), // (num classical args, num quantum args)
    Range,
    Set,
    Void,
    ToDo, // not yet implemented
    // Undefined means a type that is erroneously non-existent. This is not the same as unknown.
    // The prototypical application is trying to resolve an unbound identifier.
    Undefined,
}

// Return `true` if `ty1 == ty2` except that the `is_const`
// property is allowed to differ.
pub(crate) fn equal_up_to_constness(ty1: &Type, ty2: &Type) -> bool {
    use Type::*;
    if ty1 == ty2 {
        return true;
    }
    match (ty1, ty2) {
        // Scalars
        (Bit(_), Bit(_)) => true,
        (Duration(_), Duration(_)) => true,
        (Bool(_), Bool(_)) => true,
        (Stretch(_), Stretch(_)) => true,
        (Int(w1, _), Int(w2, _)) => w1 == w2,
        (UInt(w1, _), UInt(w2, _)) => w1 == w2,
        (Float(w1, _), Float(w2, _)) => w1 == w2,
        (Complex(w1, _), Complex(w2, _)) => w1 == w2,
        (Angle(w1, _), Angle(w2, _)) => w1 == w2,

        // Arrays: same family and same dims
        (BitArray(d1, _), BitArray(d2, _)) => d1 == d2,
        (QubitArray(d1), QubitArray(d2)) => d1 == d2,
        (IntArray(d1, w1, _), IntArray(d2,w2, _)) => d1 == d2 && w1 == w2,
        (UIntArray(d1, w1, _), UIntArray(d2,w2, _)) => d1 == d2 && w1 == w2,
        (FloatArray(d1, w1, _), FloatArray(d2,w2, _)) => d1 == d2 && w1 == w2,
        (AngleArray(d1, w1, _), AngleArray(d2,w2, _)) => d1 == d2 && w1 == w2,
        (ComplexArray(d1, w1, _), ComplexArray(d2,w2, _)) => d1 == d2 && w1 == w2,
        (BoolArray(d1,_), BoolArray(d2,_)) => d1 == d2,
        (DurationArray(d1,_), DurationArray(d2,_)) => d1 == d2,

        _ => false,
    }
}

// Are the base types of the scalars equal?
// (That is modulo width and constness?)
// Returns `false` for all array types.
fn equal_base_type(ty1: &Type, ty2: &Type) -> bool {
    use Type::*;
    matches!(
        (ty1, ty2),
        (Bit(_), Bit(_))
            | (Duration(_), Duration(_))
            | (Bool(_), Bool(_))
            | (Stretch(_), Stretch(_))
            | (Int(..), Int(..))
            | (UInt(..), UInt(..))
            | (Float(..), Float(..))
            | (Complex(..), Complex(..))
            | (Angle(..), Angle(..))
    )
}

// OQ3 supports arrays with number of dims up to seven.
// Probably exists a much better way to represent dims... [usize, N]
// Could use Box for higher dimensional arrays, or...
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ArrayDims {
    D1(usize),
    D2(usize, usize),
    D3(usize, usize, usize),
}

impl ArrayDims {
    pub fn num_dims(&self) -> usize {
        match self {
            ArrayDims::D1(..) => 1,
            ArrayDims::D2(..) => 2,
            ArrayDims::D3(..) => 3,
        }
    }

    pub fn dims(&self) -> Vec<usize> {
        match self {
            ArrayDims::D1(a) => vec![*a],
            ArrayDims::D2(a, b) => vec![*a, *b],
            ArrayDims::D3(a, b, c) => vec![*a, *b, *c],
        }
    }
}

impl Type {
    /// Return true if the type is a classical type and is neither an array type
    /// nor an array reference type.
    pub fn is_scalar(&self) -> bool {
        use Type::*;
        matches!(
            self,
            Bit(..)
                | Int(..)
                | UInt(..)
                | Float(..)
                | Angle(..)
                | Complex(..)
                | Bool(..)
                | Duration(..)
                | Stretch(..)
        )
    }

    /// Return the `Some(width)` if the type has a width `width`. Otherwise return `None`.
    /// The width of scalar types that support bit width is the bit width if present.
    /// The width of registers is the length of the register.
    pub fn width(&self) -> Width {
        use Type::*;
        match self {
            Int(w, _) | UInt(w, _) | Float(w, _) | Angle(w, _) | Complex(w, _) => *w,
            _ => None,
        }
    }

    /// Return `true` if the type has the attribute `const`.
    pub fn is_const(&self) -> bool {
        use Type::*;
        match self {
            Bit(c)
            | Int(_, c)
            | UInt(_, c)
            | Float(_, c)
            | Angle(_, c)
            | Complex(_, c)
            | Bool(c)
            | Duration(c)
            | Stretch(c)
            | BitArray(_, c) => matches!(*c, IsConst::True),
            | IntArray(_, _,c) | UIntArray(_, _,c) | FloatArray(_, _,c)
            | AngleArray(_, _,c) | ComplexArray(_, _,c)
            | BoolArray(_,c) | DurationArray(_,c) => matches!(*c, IsConst::True),
            | Qubit | QubitArray(..) | HardwareQubit => true,
            // For types without an explicit const attribute (most arrays, qubits, etc.),
            // we currently treat them as const for mutation checks elsewhere.
            _ => true,
        }
    }

    /// Return `true` if the type is a qubit or qubit register.
    pub fn is_quantum(&self) -> bool {
        matches!(self, Type::Qubit | Type::QubitArray(..) | Type::HardwareQubit)
    }

    /// Return the dimensions vector if this is an array type.
    pub fn dims(&self) -> Option<Vec<usize>> {
        use Type::*;
        match self {
            BitArray(d, _)
            | QubitArray(d)
            | IntArray(d, _, _)
            | UIntArray(d, _, _)
            | FloatArray(d, _, _)
            | AngleArray(d, _, _)
            | ComplexArray(d, _, _)
            | BoolArray(d,_)
            | DurationArray(d,_) => Some(d.dims()),
            _ => None,
        }
    }

    /// Return the number of dimensions if this is an array type.
    pub fn num_dims(&self) -> usize {
        use Type::*;
        match self {
            BitArray(d, _)
            | QubitArray(d)
            | IntArray(d, _, _)
            | UIntArray(d, _, _)
            | FloatArray(d, _, _)
            | AngleArray(d, _, _)
            | ComplexArray(d, _, _)
            | BoolArray(d,_)
            | DurationArray(d,_) => d.num_dims(),
            _ => 0,
        }
    }

    /// Return `true` if the types have the same base type.
    /// The number of dimensions and dimensions may differ.
    pub fn equal_up_to_shape(&self, other: &Type) -> bool {
        use Type::*;
        if self == other {
            return true;
        }
        matches!(
            (self, other),
            (BitArray(..), BitArray(..))
                | (QubitArray(..), QubitArray(..))
                | (IntArray(..), IntArray(..))
                | (UIntArray(..), UIntArray(..))
                | (FloatArray(..), FloatArray(..))
                | (AngleArray(..), AngleArray(..))
                | (ComplexArray(..), ComplexArray(..))
                | (BoolArray(..), BoolArray(..))
                | (DurationArray(..), DurationArray(..))
        )
    }

    /// Return `true` if the types have the same base type and the same shape.
    /// The dimensions of each axis may differ.
    pub fn equal_up_to_dims(&self, other: &Type) -> bool {
        if self == other {
            return true;
        }
        if self.num_dims() != other.num_dims() {
            return false;
        }
        self.equal_up_to_shape(other)
    }
}

#[test]
fn test_type_enum1() {
    let t = Type::Bit(IsConst::False);
    assert!(!t.is_const());
    assert!(t.width().is_none());
    assert!(!t.is_quantum());
    assert!(t.is_scalar());
}

#[test]
fn test_type_enum2() {
    let t = Type::Qubit;
    assert!(t.is_const());
    assert!(t.width().is_none());
    assert!(t.is_quantum());
    assert!(!t.is_scalar());
}

//
// Promotion
//

// `const` is less than non-`const`.
// (why does this look like the opposite of correct definition?)
fn promote_constness(ty1: &Type, ty2: &Type) -> IsConst {
    IsConst::from(ty1.is_const() && ty2.is_const())
}

// Return greater of the `Width`s of the types.
// The width `None` is the greatest width.
fn promote_width(ty1: &Type, ty2: &Type) -> Width {
    match (ty1.width(), ty2.width()) {
        (Some(width1), Some(width2)) => Some(std::cmp::max(width1, width2)),
        (Some(_), None) | (None, Some(_)) | (None, None) => None,
    }
}

pub fn promote_types_not_equal(ty1: &Type, ty2: &Type) -> Type {
    let typ = promote_types_symmetric(ty1, ty2);
    if typ != Type::Void {
        return typ;
    }
    let typ = promote_types_asymmetric(ty1, ty2);
    if typ == Type::Void {
        return promote_types_asymmetric(ty2, ty1);
    }
    typ
}

// promotion suitable for some binary operations, eg +, -, *
pub fn promote_types(ty1: &Type, ty2: &Type) -> Type {
    if equal_up_to_constness(ty1, ty2) {
        return ty1.clone();
    }
    let typ = promote_types_symmetric(ty1, ty2);
    if typ != Type::Void {
        return typ;
    }
    let typ = promote_types_asymmetric(ty1, ty2);
    if typ == Type::Void {
        return promote_types_asymmetric(ty2, ty1);
    }
    typ
}

fn promote_types_symmetric(ty1: &Type, ty2: &Type) -> Type {
    use Type::*;
    let isconst = promote_constness(ty1, ty2);
    match (ty1, ty2) {
        (Int(..), Int(..)) => Int(promote_width(ty1, ty2), isconst),
        (UInt(..), UInt(..)) => UInt(promote_width(ty1, ty2), isconst),
        (Float(..), Float(..)) => Float(promote_width(ty1, ty2), isconst),
        _ => Void,
    }
}

fn promote_types_asymmetric(ty1: &Type, ty2: &Type) -> Type {
    use Type::*;
    match (ty1, ty2) {
        (Int(..), Float(..)) => ty2.clone(),
        (UInt(..), Float(..)) => ty2.clone(),
        (Float(..), Complex(..)) => ty2.clone(),
        _ => Void,
    }
}

/// Can the literal type be cast to type `ty1` for assignment?
/// The width of a literal is a fiction that is not in the spec.
/// So when casting, the width does not matter.
///
/// We currently have `128` for the width of a literal `Int`.
/// and the literal parsed into a Rust `u128` plus a bool for
/// a sign. We need to check, outside of the semantics whether
/// the value of type `u128` can be cast to the lhs type.
/// For that, we need the value. `can_cast_literal` does not
/// know the value.
pub fn can_cast_literal(ty1: &Type, ty_lit: &Type) -> bool {
    use Type::*;
    if equal_base_type(ty1, ty_lit) {
        return true;
    }
    match (ty1, ty_lit) {
        (Float(..), Int(..)) => true,
        (Float(..), UInt(..)) => true,
        (Complex(..), Float(..)) => true,
        (Complex(..), Int(..)) => true,
        (Complex(..), UInt(..)) => true,

        // Listing these explicitly is slower, but
        // might be better for maintaining and debugging.
        (Int(..), Float(..)) => false,
        (UInt(..), Float(..)) => false,
        (Int(..), Complex(..)) => false,
        (UInt(..), Complex(..)) => false,
        _ => false,
    }
}
