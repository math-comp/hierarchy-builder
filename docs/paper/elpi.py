# -*- coding: utf-8 -*-
"""
    pygments.lexers.elpi
    ~~~~~~~~~~~~~~~~~~~~~~

    Lexers for Elpi.

    :copyright: Copyright 2006-2019 by the Pygments team, see AUTHORS.
    :license: BSD, see LICENSE for details.
"""

import re

from pygments.lexer import RegexLexer, bygroups, using
from pygments.token import Text, Comment, Operator, Keyword, Name, String, \
    Number, Punctuation
from pygments.lexers.theorem import CoqLexer

__all__ = ['ElpiLexer']


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
            (r'(term|record-decl|indt-decl|@mixinname|@structurename|@factoryname|universe|list|pair|gref)\b(?!-)', Name.Class),
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
             String.Text),  # atom, characters
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

