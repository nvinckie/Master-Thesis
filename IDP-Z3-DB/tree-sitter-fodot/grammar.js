module.exports = grammar({
  name: 'fodot',

  rules: {
    source_file: $ => repeat1($.block),

    // Vocabulary, theory, and structure.
    block: $ => choice(
      seq(
        'vocabulary',
        $.block_voc
      ), 
      seq(
        'theory',
        $.block_theory
      ),
      seq(
        'structure',
        $.block_structure
      )
    ),

    block_voc: $ => seq(
      optional($.block_name),
      '{',
      repeat(choice($.declaration, $._line_comment)),
      '}'
    ),

    block_name: $ => /[\w\d]+/,

    declaration: $ => choice(
      $.type_declaration,
      $.prop_declaration,
      $.constant_declaration,
      $.predicate_declaration,
      $.function_declaration
    ),
      
    type_declaration: $ => seq(
      'type',
      $.symbol_name,
      optional($.symbol_interpretation)
    ),

    prop_declaration: $ => seq(
      $.symbol_name,
      ':',
      optional('('),
      optional(')'),
      '->',
      'Bool',
    ),

    constant_declaration: $ => seq(
      $.symbol_name,
      ':',
      optional('('),
      optional(')'),
      '->',
      choice($.builtin_type, $.symbol_name)
    ),

    predicate_declaration: $ => seq(
      $.symbol_name,
      ':',
      optional('('),
      repeat1(seq($.symbol_name, optional('*'))),
      optional(')'),
      '->',
      'Bool'
    ),

    function_declaration: $ => seq(
      $.symbol_name,
      ':',
      optional('('),
      repeat1(seq($.symbol_name, optional('*'))),
      optional(')'),
      '->',
      choice($.builtin_type, $.symbol_name),
    ),

    symbol_name: $ => prec(20, /[\w\d]+/),

    builtin_type: $ => choice(
      'Int',
      'Real',
      'Date',
    ),

    block_theory: $ => seq(
      optional(seq($.block_name, ':', $.block_name)),
      '{',
      repeat(choice(seq($.formula, '.'), $.definition, $._line_comment)),
      '}'
    ),

    formula: $ => choice(
      $.applied_symbol,
      $.type_element,
      $.land,
      $.lor,
      $.neg,
      $._brackets,
      $.implication,
      $.equivalence,
      $.sum,
      $.subtraction,
      $.multiplication,
      $.division,
      $.modulo,
      $._comparison,
      $.universal,
      $.existential,
      $.in_operator,
    ),

    applied_symbol: $ => seq(
      $.symbol_name,
      '(',
      optional(
        seq(
          repeat(seq($.formula, ',')),
          $.formula)
        ),
      ')',
    ),

    land: $ => prec.left(7, seq(
      $.formula,
      '&',
      $.formula,
    )),

    lor: $ => prec.left(8, seq(
      $.formula,
      '|',
      $.formula,
    )),

    neg: $ => prec.left(17, seq(
      '~',
      $.formula,
    )),

    // Don't show brackets in the AST
    _brackets: $ => seq('(', $.formula, ')'),

    implication: $ => choice($._rimplication, $._limplication),

    _rimplication: $ => prec.right(6, seq(
      $.formula,
      '=>',
      $.formula
    )),

    _limplication: $ => prec.left(6, seq(
      $.formula,
      '<=',
      $.formula
    )),

    equivalence: $ => prec.left(6, seq(
      $.formula,
      '<=>',
      $.formula
    )),

    sum: $ => prec.left(11, seq(
      $.formula,
      '+',
      $.formula
    )),

    subtraction: $ => prec.left(11, seq(
      $.formula,
      '-',
      $.formula
    )),

    multiplication: $ => prec.left(10, seq(
      $.formula,
      '*',
      $.formula,
    )),

    division: $ => prec.left(10, seq(
      $.formula,
      '/',
      $.formula,
    )),

    modulo: $ => prec.left(9, seq(
      $.formula,
      '%',
      $.formula,
    )),


    _comparison: $ => prec.left(8, choice(
      $.equality,
      $.ge,
      $.le,
      $.geq,
      $.leq,
      $.inequality
    )),

    equality: $ => prec.left(10, seq(
      $.formula,
      '=',
      $.formula,
    )),

    inequality: $ => prec.left(10, seq(
      $.formula,
      '~=',
      $.formula,
    )),

    ge: $ => prec.left(8, seq(
      $.formula,
      '>',
      $.formula,
    )),

    le: $ => prec.left(8, seq(
      $.formula,
      '<',
      $.formula,
    )),

    geq: $ => prec.left(8, seq(
      $.formula,
      '>=',
      $.formula,
    )),

    leq: $ => prec.left(8, seq(
      $.formula,
      '=<',
      $.formula,
    )),

    quantification: $ => prec.left(5, seq(
      optional(repeat(seq($.variable, ','))),
      $.variable,
      'in',
      $.symbol_name,
    )),

    universal: $ => prec.left(5, seq(
      '!',
      $.quantification,
      optional(repeat(seq(',', $.quantification))),
      ':',
      $.formula
    )),

    existential: $ => prec.left(5, seq(
      '?',
      $.quantification,
      optional(repeat(seq(',', $.quantification))),
      ':',
      $.formula
    )),


    variable: $ => /[\w\d]+/,

    in_operator: $ => prec.left(6, seq(
        $.formula,
        'in',
        '{',
        $.type_element,
        optional(repeat(seq(',', $.type_element))),
        '}'
    )),

    definition: $ => seq(
        '{',
        repeat1($.definitional_rule),
        '}',
    ),

    definitional_rule: $ => seq(
        $.formula,
        '<-',
        $.formula,
        '.'
    ),

    block_structure: $ => seq(
      optional(seq($.block_name, ':', $.block_name)),
      '{',
      repeat(choice(seq($.symbol_name, $.symbol_interpretation, '.'), $._line_comment)),
      '}'
    ),

    // TODO: also add bool and constant
    symbol_interpretation: $ => seq(
        ':=',
        '{',
        optional(  // Optional, because the interpretation could also be left empty.
          choice(
            $.element_enumeration,
            $.range_enumeration,
            $.predicate_enumeration,
            $.function_enumeration,
          ),
        ),
        '}',
        optional(seq('else', $.type_element))
    ),

    element_enumeration: $ => repeat1(
      seq(
        $.type_element,
        optional(','),
    )),

    range_enumeration: $ => seq(
      $.type_element,
      '..',
      $.type_element,
    ),

    predicate_enumeration: $ => repeat1(seq(
      '(',
      $.element_enumeration,
      ')',
      optional(',')
    )),

    function_enumeration: $ => choice(
      // Distinguish between 1-ary and >1-ary
      repeat1(seq('(', $.element_enumeration, ')', '->', $.type_element, optional(','))),
      repeat1(seq($.element_enumeration, '->', $.type_element, optional(','))),
    ),

    type_element: $ => choice(
      $._string,
      $._int,
      $._float,
      // $._date //TODO!
      ///[\w\d]+/,
    ),

    _string: $ => prec(21, /[\w\d]+/),

    _int: $ => /-?[\d]+/,

    _float: $ => /-?[\d]+\.[\d]+/,

    _line_comment: $ => /(?:\/\/.*?$|\[.*?\])/

  }
});

