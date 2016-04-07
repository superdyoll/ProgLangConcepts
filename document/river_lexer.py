# -*- coding: utf-8 -*-
"""
    pygments.lexers.river_lexer
    ~~~~~~~~~~~~~~~~~~~~~~

    Lexers for our language: River

    :copyright: Copyright 2016 by the River Team (Andy and Lloyd)
    :license: BSD, probably.
"""

import re

from pygments.lexer import Lexer, RegexLexer, include, bygroups, using, \
    default, words, combined, do_insertions
from pygments.util import get_bool_opt, shebang_matches
from pygments.token import Text, Comment, Operator, Keyword, Name, String, \
    Number, Punctuation, Generic, Other, Error
from pygments import unistring as uni

__all__ = ['RiverLexer']

line_re = re.compile('.*?\n')


class RiverLexer(RegexLexer):
    """
    For River source code.
    """

    name = 'River'
    aliases = ['river']
    filenames = ['*.spl']

    tokens = {
        'root': [
            (r'\n', Text),
            (r'//.*?\n', Comment.Single),
            (r'(/\*(?:.|\n)*?\*/)', Comment.Multiline),
            (r'[^\S\n]+', Text),
            (r'[]{}:(),;[]', Punctuation),
            (r'\\\n', Text),
            (r'\\', Text),
            (r'(in|is|and|or|not)\b', Operator.Word),
            (r'!=|==|<<|>>|::|[-~+/*%=<>&|.]', Operator),
            include('keywords'),
            include('builtins'),
            (r'(lambda)((?:\s|\\\s)+)', bygroups(Keyword, Text), 'funcname'),
            include('name'),
            include('numbers'),
        ],
        'keywords': [
            (words(('if', 'lambda', 'else'), suffix=r'\b'),
             Keyword),
        ],
        'builtins': [
            (words(('read','int',r'stream<.*?>'), suffix=r'\b'),
             Keyword),
        ],
        'numbers': [
            (r'\d+j?', Number.Integer)
        ],
        'name': [
            ('[a-zA-Z_-]+', Name),
        ],
        'funcname': [
            ('[a-zA-Z_]\w*', Name.Function, '#pop')
        ],
    }