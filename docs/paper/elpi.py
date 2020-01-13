# -*- coding: utf-8 -*-
"""
    pygments.lexers.elpi
    ~~~~~~~~~~~~~~~~~~~~~~

    Lexers for Coq-Elpi.

    :copyright: Copyright 2006-2019 by the Pygments team, see AUTHORS.
    :license: BSD, see LICENSE for details.
"""

import re

from pygments.lexer import RegexLexer, bygroups, using, words, default
from pygments.token import Text, Comment, Operator, Keyword, Name, String, \
    Number, Punctuation
from pygments.lexers.theorem import CoqLexer

__all__ = ['ElpiLexer', 'CoqElpiLexer']

class ElpiLexer(RegexLexer):
    """
    Lexer for Elpi files.
    """
    name = 'elpi'
    aliases = ['elpi']
    filenames = ['*.elpi']
    mimetypes = ['text/x-elpi']

    flags = re.UNICODE | re.MULTILINE

    tokens = {
        'root': [
            (r'/\*', Comment.Multiline, 'nested-comment'),
            (r'%.*', Comment.Single),
            # quotation
            (r'({{)([^}]*)(}})', bygroups(Punctuation,using(CoqLexer),Punctuation)),
            # character literal
            (r'0\'.', String.Char),
            (r'0b[01]+', Number.Bin),
            (r'0o[0-7]+', Number.Oct),
            (r'0x[0-9a-fA-F]+', Number.Hex),
            # literal with prepended base
            (r'(tt|ff)\b', Number.Integer),
            (r'\d\d?\'[a-zA-Z0-9]+', Number.Integer),
            (r'(\d+\.\d*|\d*\.\d+)([eE][+-]?[0-9]+)?', Number.Float),
            (r'\d+', Number.Integer),
            (r'[\[\](){}|.,;!]', Punctuation),
            (r'"(?:\\x[0-9a-fA-F]+\\|\\u[0-9a-fA-F]{4}|\\U[0-9a-fA-F]{8}|'
             r'\\[0-7]+\\|\\["\nabcefnrstv]|[^\\"])*"', String),
            (r"'(?:''|[^'])*'", String.Atom),  # quoted atom
            # Needs to not be followed by an atom.
            # (r'=(?=\s|[a-zA-Z\[])', Operator),
            (r'(\^|<|>|=<|>=|==|=:=|=|/|//|\*|\+|-)(?=\s|[a-zA-Z0-9\[])',
             Keyword),
            (r'(mod|div|not)\b', Operator),
            (r'(global|indt|indc|field|record|end-record|const|app|some|fun|sort)\b(?!-)', Operator),
            (r'_', Keyword),  # The don't-care variable
            (r'^\s*pred\s', Keyword),
            (r'^\s*external pred\s', Keyword),
            (r'\s[io]:', Keyword),
            (r'(:-|pi\b(?!-)|=>|\\|kind\b(?!-)|type\b(?!-)|is\b(?!-)|!)', Keyword),
            (r'(term|record-decl|indt-decl|mixinname|structurename|factoryname|universe|list|pair|gref)\b(?!-)', Name.Class),
            (r'(string|bool|constant|inductive|constructor)\b', String.Atom),
            (r'(std|coq|CS|env|elpi)(\.)', bygroups(Name.Builtin, Punctuation)),
            (u'([a-z\u00c0-\u1fff\u3040-\ud7ff\ue000-\uffef]'
             u'[\\w$\u00c0-\u1fff\u3040-\ud7ff\ue000-\uffef]*)'
             u'(\\s*)(:-|-->)',
             bygroups(Name.Function, Text, Operator)),  # function defn
            (u'([a-z\u00c0-\u1fff\u3040-\ud7ff\ue000-\uffef]'
             u'[\\w$\u00c0-\u1fff\u3040-\ud7ff\ue000-\uffef]*)'
             u'(\\s*)(\\()',
             bygroups(Name.Function, Text, Punctuation)),
            (u'[a-z\u00c0-\u1fff\u3040-\ud7ff\ue000-\uffef]'
             u'[\\w\-!?$\u00c0-\u1fff\u3040-\ud7ff\ue000-\uffef]*',
             Name),  # atom, characters
            # This one includes !
            (u'[#&*+\\-./:<=>?@\\\\^~\u00a1-\u00bf\u2010-\u303f]+',
             String.Atom),  # atom, graphics
            (r'[A-Z_]\w*', Name.Variable),
            (u'\\s+|[\u2000-\u200f\ufff0-\ufffe\uffef]', Text),
        ],
        'nested-comment': [
            (r'\*/', Comment.Multiline, '#pop'),
            (r'/\*', Comment.Multiline, '#push'),
            (r'[^*/]+', Comment.Multiline),
            (r'[*/]', Comment.Multiline),
        ],
    }

    def analyse_text(text):
        return ':-' in text

class CoqElpiLexer(RegexLexer):
    """
    For the `Coq <http://coq.inria.fr/>`_ theorem prover.

    .. versionadded:: 1.5
    """

    name = 'CoqElpi'
    aliases = ['coqelpi']
    filenames = ['*.v']
    mimetypes = ['text/x-coqelpi']

    keywords1 = (
        # Vernacular commands
        'Section', 'Module', 'End', 'Require', 'Import', 'Export', 'Variable',
        'Variables', 'Parameter', 'Parameters', 'Axiom', 'Hypothesis',
        'Hypotheses', 'Notation', 'Local', 'Tactic', 'Reserved', 'Scope',
        'Open', 'Close', 'Bind', 'Delimit', 'Definition', 'Let', 'Ltac',
        'Fixpoint', 'CoFixpoint', 'Morphism', 'Relation', 'Implicit',
        'Arguments', 'Set', 'Unset', 'Contextual', 'Strict', 'Prenex',
        'Implicits', 'Inductive', 'CoInductive', 'Record', 'Structure',
        'Canonical', 'Coercion', 'Theorem', 'Lemma', 'Corollary',
        'Proposition', 'Fact', 'Remark', 'Example', 'Proof', 'Goal', 'Save',
        'Qed', 'Defined', 'Hint', 'Resolve', 'Rewrite', 'View', 'Search',
        'Show', 'Print', 'Printing', 'All', 'Graph', 'Projections', 'inside',
        'outside', 'Check', 'Global', 'Instance', 'Class', 'Existing',
        'Universe', 'Polymorphic', 'Monomorphic', 'Context', 'Elpi', 'Accumulate', 'Db', 'Command'
    )
    keywords2 = (
        # Gallina
        'forall', 'exists', 'exists2', 'fun', 'fix', 'cofix', 'struct',
        'match', 'end',  'in', 'return', 'let', 'if', 'is', 'then', 'else',
        'for', 'of', 'nosimpl', 'with', 'as',
    )
    keywords3 = (
        # Sorts
        'Type', 'Prop',
    )
    keywords4 = (
        # Tactics
        'pose', 'set', 'move', 'case', 'elim', 'apply', 'clear', 'hnf', 'intro',
        'intros', 'generalize', 'rename', 'pattern', 'after', 'destruct',
        'induction', 'using', 'refine', 'inversion', 'injection', 'rewrite',
        'congr', 'unlock', 'compute', 'ring', 'field', 'replace', 'fold',
        'unfold', 'change', 'cutrewrite', 'simpl', 'have', 'suff', 'wlog',
        'suffices', 'without', 'loss', 'nat_norm', 'assert', 'cut', 'trivial',
        'revert', 'bool_congr', 'nat_congr', 'symmetry', 'transitivity', 'auto',
        'split', 'left', 'right', 'autorewrite', 'tauto', 'setoid_rewrite',
        'intuition', 'eauto', 'eapply', 'econstructor', 'etransitivity',
        'constructor', 'erewrite', 'red', 'cbv', 'lazy', 'vm_compute',
        'native_compute', 'subst',
    )
    keywords5 = (
        # Terminators
        'by', 'done', 'exact', 'reflexivity', 'tauto', 'romega', 'omega',
        'assumption', 'solve', 'contradiction', 'discriminate',
        'congruence',
    )
    keywords6 = (
        # Control
        'do', 'last', 'first', 'try', 'idtac', 'repeat',
    )
    # 'as', 'assert', 'begin', 'class', 'constraint', 'do', 'done',
    # 'downto', 'else', 'end', 'exception', 'external', 'false',
    # 'for', 'fun', 'function', 'functor', 'if', 'in', 'include',
    # 'inherit', 'initializer', 'lazy', 'let', 'match', 'method',
    # 'module', 'mutable', 'new', 'object', 'of', 'open', 'private',
    # 'raise', 'rec', 'sig', 'struct', 'then', 'to', 'true', 'try',
    # 'type', 'val', 'virtual', 'when', 'while', 'with'
    keyopts = (
        '!=', '#', '&', '&&', r'\(', r'\)', r'\*', r'\+', ',', '-', r'-\.',
        '->', r'\.', r'\.\.', ':', '::', ':=', ':>', ';', ';;', '<', '<-',
        '<->', '=', '>', '>]', r'>\}', r'\?', r'\?\?', r'\[', r'\[<', r'\[>',
        r'\[\|', ']', '_', '`', r'\{', r'\{<', r'\|', r'\|]', r'\}', '~', '=>',
        r'/\\', r'\\/', r'\{\|', r'\|\}',
        u'Π', u'λ',
    )
    operators = r'[!$%&*+\./:<=>?@^|~-]'
    prefix_syms = r'[!?~]'
    infix_syms = r'[=<>@^|&+\*/$%-]'
    flags = re.DOTALL | re.MULTILINE
    tokens = {
        'root': [
            (r'(lp:{{)(.*?)(}}\.)', bygroups(Punctuation,using(ElpiLexer),Punctuation)),
            (r'\s+', Text),
            (r'false|true|\(\)|\[\]', Name.Builtin.Pseudo),
            (r'\(\*', Comment, 'comment'),
            (words(keywords1, prefix=r'\b', suffix=r'\b'), Keyword.Namespace),
            (words(keywords2, prefix=r'\b', suffix=r'\b'), Keyword),
            (words(keywords3, prefix=r'\b', suffix=r'\b'), Keyword.Type),
            (words(keywords4, prefix=r'\b', suffix=r'\b'), Keyword),
            (words(keywords5, prefix=r'\b', suffix=r'\b'), Keyword.Pseudo),
            (words(keywords6, prefix=r'\b', suffix=r'\b'), Keyword.Reserved),
            # (r'\b([A-Z][\w\']*)(\.)', Name.Namespace, 'dotted'),
            (r'\b([A-Z][\w\']*)', Name),
            (r'(%s)' % '|'.join(keyopts[::-1]), Operator),
            (r'(%s|%s)?%s' % (infix_syms, prefix_syms, operators), Operator),

            (r"[^\W\d][\w']*", Name),

            (r'\d[\d_]*', Number.Integer),
            (r'0[xX][\da-fA-F][\da-fA-F_]*', Number.Hex),
            (r'0[oO][0-7][0-7_]*', Number.Oct),
            (r'0[bB][01][01_]*', Number.Bin),
            (r'-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)', Number.Float),

            (r"'(?:(\\[\\\"'ntbr ])|(\\[0-9]{3})|(\\x[0-9a-fA-F]{2}))'",
             String.Char),
            (r"'.'", String.Char),
            (r"'", Keyword),  # a stray quote is another syntax element

            (r'"', String.Double, 'string'),

            (r'[~?][a-z][\w\']*:', Name),


        ],
        'comment': [
            (r'[^(*)]+', Comment),
            (r'\(\*', Comment, '#push'),
            (r'\*\)', Comment, '#pop'),
            (r'[(*)]', Comment),
        ],
        'string': [
            (r'[^"]+', String.Double),
            (r'""', String.Double),
            (r'"', String.Double, '#pop'),
        ],
        'dotted': [
            (r'\s+', Text),
            (r'\.', Punctuation),
            (r'[A-Z][\w\']*(?=\s*\.)', Name.Namespace),
            (r'[A-Z][\w\']*', Name.Class, '#pop'),
            (r'[a-z][a-z0-9_\']*', Name, '#pop'),
            default('#pop')
        ],
    }

    def analyse_text(text):
        if text.startswith('(*'):
            return True
