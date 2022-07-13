# ------------------------------------------------------------------------------
# CodeHawk Binary Analyzer
# Author: Henny Sipma
# ------------------------------------------------------------------------------
# The MIT License (MIT)
#
# Copyright (c) 2022 Aarno Labs, LLC
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
# ------------------------------------------------------------------------------
"""Main interface to the AST library."""

from typing import Any, Dict, List

from chb.ast.AbstractSyntaxTree import AbstractSyntaxTree
from chb.ast.ASTCPrettyPrinter import ASTCPrettyPrinter
from chb.ast.ASTDeserializer import ASTDeserializer
from chb.ast.ASTFunction import ASTFunction
from chb.ast.ASTSerializer import ASTSerializer
from chb.ast.ASTSymbolTable import ASTGlobalSymbolTable, ASTLocalSymbolTable
from chb.ast.CustomASTSupport import CustomASTSupport


class ASTApplicationInterface:

    def __init__(self, support: CustomASTSupport = CustomASTSupport()) -> None:
        self._support = support
        self._globalsymboltable = ASTGlobalSymbolTable()
        self._fnsdata: List[Dict[str, Any]] = []

    @property
    def support(self) -> CustomASTSupport:
        return self._support

    @property
    def globalsymboltable(self) -> ASTGlobalSymbolTable:
        return self._globalsymboltable

    def add_function(self, astfn: ASTFunction, verbose: bool = False) -> None:

        localsymboltable = ASTLocalSymbolTable(self.globalsymboltable)
        if astfn.has_function_prototype():
            localsymboltable.set_function_prototype(astfn.function_prototype())

        astree = AbstractSyntaxTree(astfn.address, astfn.name, localsymboltable)

        try:
            cfg_ast = astfn.cfg_ast(astree, self.support)
            ast = astfn.ast(astree, self.support)
        except Exception as e:
            print("=" * 80)
            print("Error in ast generation of " + astfn.name)
            print(str(e))
            print("*" * 80)
            return

        if verbose:
            print("\n")
            pp = ASTCPrettyPrinter(localsymboltable)
            print(pp.to_c(ast))
            print(pp.to_c(cfg_ast))

        fndata: Dict[str, Any] = {}
        serializer = ASTSerializer()

        localsymboltable.serialize(serializer)
        protoindex = localsymboltable.serialize_function_prototype(serializer)
        ast_startindex = serializer.index_stmt(ast)
        cfg_startindex = serializer.index_stmt(cfg_ast)
        astnodes = serializer.records()

        fndata["name"] = astfn.name
        fndata["va"] = astfn.address
        fndata["prototype"] = protoindex
        fndata["ast"] = {}
        fndata["ast"]["nodes"] = astnodes
        fndata["ast"]["ast-startnode"] = ast_startindex
        fndata["ast"]["cfg-ast-startnode"] = cfg_startindex
        fndata["spans"] = astree.spans
        fndata["available-expressions"] = {}

        self._fnsdata.append(fndata)

    def serialize(self, verbose: bool = False) -> Dict[str, Any]:
        globalserializer = ASTSerializer()
        self.globalsymboltable.serialize(globalserializer)

        ast_output: Dict[str, Any] = {}
        ast_output["global-symbol-table"] = globalserializer.records()
        ast_output["functions"] = self._fnsdata

        if verbose:
            print("\nDeserialized ast output")
            print("-----------------------")
            deserializer = ASTDeserializer(ast_output)
            for (symtable, ast) in deserializer.functions.values():
                pp = ASTCPrettyPrinter(symtable)
                print("\n")
                print(pp.to_c(ast))

        return ast_output
                  

    

        

        

        

        
