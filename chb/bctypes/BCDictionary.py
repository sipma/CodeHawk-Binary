# ------------------------------------------------------------------------------
# CodeHawk Binary Analyzer
# Author: Henny Sipma
# ------------------------------------------------------------------------------
# The MIT License (MIT)
#
# Copyright (c) 2021-2024 Aarno Labs LLC
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
"""Dictionary of CIL-types as produced by the CIL parser."""

from typing import (
    Any, Callable, cast, Dict, List, Optional, Tuple, TYPE_CHECKING)

import xml.etree.ElementTree as ET

from chb.bctypes.BCAttribute import BCAttribute, BCAttributes
from chb.bctypes.BCAttrParam import BCAttrParam
from chb.bctypes.BCDictionaryRecord import BCDictionaryRecord, bcregistry
from chb.bctypes.BCCompInfo import BCCompInfo
from chb.bctypes.BCConstant import BCConstant
from chb.bctypes.BCEnumInfo import BCEnumInfo
from chb.bctypes.BCEnumItem import BCEnumItem
from chb.bctypes.BCExp import BCExp
from chb.bctypes.BCFieldInfo import BCFieldInfo
from chb.bctypes.BCFunArgs import BCFunArg, BCFunArgs
from chb.bctypes.BCLHost import BCLHost
from chb.bctypes.BCLval import BCLval
from chb.bctypes.BCOffset import BCOffset
from chb.bctypes.BCTyp import BCTyp, BCTypNamed
from chb.bctypes.BCTypSig import BCTypSig, BCTypSigList
from chb.bctypes.BCTypeInfo import BCTypeInfo
from chb.bctypes.BCVarInfo import BCVarInfo

import chb.util.fileutil as UF
import chb.util.IndexedTable as IT
import chb.util.StringIndexedTable as SI

if TYPE_CHECKING:
    from chb.app.AppAccess import AppAccess


class BCDictionary:

    def __init__(
            self,
            app: "AppAccess",
            xnode: Optional[ET.Element]) -> None:
        self._app = app
        self.string_table = SI.StringIndexedTable("string-table")
        self.attrparam_table = IT.IndexedTable("attrparam-table")
        self.attributes_table = IT.IndexedTable("attributes-table")
        self.attribute_table = IT.IndexedTable("attribute-table")
        self.constant_table = IT.IndexedTable("constant-table")
        self.exp_table = IT.IndexedTable("exp-table")
        self.funarg_table = IT.IndexedTable("funarg-table")
        self.funargs_table = IT.IndexedTable("funargs-table")
        self.lhost_table = IT.IndexedTable("lhost-table")
        self.lval_table = IT.IndexedTable("lval-table")
        self.offset_table = IT.IndexedTable("offset-table")
        self.typ_table = IT.IndexedTable("typ-table")
        self.location_table = IT.IndexedTable("location-table")
        self.initinfo_table = IT.IndexedTable("initinfo-table")
        self.typeinfo_table = IT.IndexedTable("typeinfo-table")
        self.typsig_table = IT.IndexedTable("typsig-table")
        self.typsiglist_table = IT.IndexedTable("typsiglist-table")
        self.varinfo_table = IT.IndexedTable("varinfo-table")
        self.fieldinfo_table = IT.IndexedTable("fieldinfo-table")
        self.compinfo_table = IT.IndexedTable("compinfo-table")
        self.enumitem_table = IT.IndexedTable("enumitem-table")
        self.enuminfo_table = IT.IndexedTable("enuminfo-table")
        self.tables = [
            self.attributes_table,
            self.attribute_table,
            self.attrparam_table,
            self.constant_table,
            self.exp_table,
            self.funarg_table,
            self.funargs_table,
            self.lhost_table,
            self.lval_table,
            self.offset_table,
            self.typ_table,
            self.location_table,
            self.initinfo_table,
            self.typeinfo_table,
            self.typsig_table,
            self.typsiglist_table,
            self.varinfo_table,
            self.fieldinfo_table,
            self.compinfo_table,
            self.enumitem_table,
            self.enuminfo_table
        ]
        self.typeinfo_names: Dict[str, BCTypeInfo] = {}
        self.compinfo_keys: Dict[int, BCCompInfo] = {}
        self.enuminfo_names: Dict[str, BCEnumInfo] = {}
        self.initialize(xnode)

    @property
    def app(self) -> "AppAccess":
        return self._app

    # ------------------------- retrieve items by name/key ---------------------

    def has_typeinfo_by_name(self, name: str) -> bool:
        return name in self.typeinfo_names

    def typeinfo_by_name(self, name: str) -> BCTypeInfo:
        if name in self.typeinfo_names:
            return self.typeinfo_names[name]
        else:
            raise UF.CHBError("Type-info name " + name + " not found")

    def compinfo_by_key(self, key: int) -> BCCompInfo:
        if key in self.compinfo_keys:
            return self.compinfo_keys[key]
        else:
            raise UF.CHBError("Compinfo key " + str(key) + " not found")

    def enuminfo_by_name(self, name: str) -> BCEnumInfo:
        if name in self.enuminfo_names:
            return self.enuminfo_names[name]
        else:
            raise UF.CHBError("Enuminfo name " + name + " not found")

    # ------------------------- retrieve items from dictionary tables ----------

    def string(self, ix: int) -> str:
        return self.string_table.retrieve(ix)

    def attrparam(self, ix: int) -> BCAttrParam:
        return bcregistry.mk_instance(
            self, self.attrparam_table.retrieve(ix), BCAttrParam)

    def attribute(self, ix: int) -> BCAttribute:
        return BCAttribute(self, self.attribute_table.retrieve(ix))

    def attributes(self, ix: int) -> Optional[BCAttributes]:
        if ix == -1:
            return None
        else:
            return BCAttributes(self, self.attributes_table.retrieve(ix))

    def constant(self, ix: int) -> BCConstant:
        return bcregistry.mk_instance(
            self, self.constant_table.retrieve(ix), BCConstant)

    def exp(self, ix: int) -> BCExp:
        return bcregistry.mk_instance(
            self, self.exp_table.retrieve(ix), BCExp)

    def funarg(self, ix: int) -> BCFunArg:
        return BCFunArg(self, self.funarg_table.retrieve(ix))

    def funargs(self, ix: int) -> BCFunArgs:
        return BCFunArgs(self, self.funargs_table.retrieve(ix))

    def lhost(self, ix: int) -> BCLHost:
        return bcregistry.mk_instance(
            self, self.lhost_table.retrieve(ix), BCLHost)

    def lval(self, ix: int) -> BCLval:
        return BCLval(self, self.lval_table.retrieve(ix))

    def offset(self, ix: int) -> BCOffset:
        return bcregistry.mk_instance(
            self, self.offset_table.retrieve(ix), BCOffset)

    def typ(self, ix: int) -> BCTyp:
        return bcregistry.mk_instance(
            self, self.typ_table.retrieve(ix), BCTyp)

    def typeinfo(self, ix: int) -> BCTypeInfo:
        tinfo = BCTypeInfo(self, self.typeinfo_table.retrieve(ix))
        self.typeinfo_names[tinfo.tname] = tinfo
        return tinfo

    def typsig(self, ix: int) -> BCTypSig:
        return bcregistry.mk_instance(
            self, self.typsig_table.retrieve(ix), BCTypSig)

    def optional_typsig_list(self, ix: int) -> Optional[BCTypSigList]:
        if ix == -1:
            return None
        return BCTypSigList(self, self.typsiglist_table.retrieve(ix))

    def varinfo(self, ix: int) -> BCVarInfo:
        return BCVarInfo(self, self.varinfo_table.retrieve(ix))

    def compinfo(self, ix: int) -> BCCompInfo:
        cinfo = BCCompInfo(self, self.compinfo_table.retrieve(ix))
        self.compinfo_keys[cinfo.ckey] = cinfo
        return cinfo

    def enuminfo(self, ix: int) -> BCEnumInfo:
        einfo = BCEnumInfo(self, self.enuminfo_table.retrieve(ix))
        self.enuminfo_names[einfo.ename] = einfo
        return einfo

    def enumitem(self, ix: int) -> BCEnumItem:
        eitem = BCEnumItem(self, self.enumitem_table.retrieve(ix))
        return BCEnumItem(self, eitem)

    def fieldinfo(self, ix: int) -> BCFieldInfo:
        return BCFieldInfo(self, self.fieldinfo_table.retrieve(ix))

    # -------------------------------------- add new objects -------------------

    def ptr_to(self, t: BCTyp) -> BCTyp:
        tags = ["tptr"]
        args = [t.index]
        key = IT.get_key(tags, args)

        def f(ix: int,
              key: Tuple[str, str]) -> BCTyp:
            itv = IT.IndexedTableValue(ix, tags, args)
            return bcregistry.mk_instance(self, itv, BCTyp)

        index = self.typ_table.add(key, f)
        return self.typ(index)

    # -------------------------- initialize dictionary from file ---------------

    def initialize(self, xnode: Optional[ET.Element]) -> None:
        if xnode is not None:
            for t in self.tables:
                xtable = xnode.find(t.name)
                if xtable is not None:
                    t.reset()
                    t.read_xml(xtable, "n")
                else:
                    raise UF.CHBError(
                        "Table " + t.name + " not found in bcdictionary")
            self.string_table.reset()
            xstable = xnode.find(self.string_table.name)
            if xstable is not None:
                self.string_table.read_xml(xstable)
            else:
                raise UF.CHBError(
                    "Error reading stringtable " + self.string_table.name)
            for ix in self.typeinfo_table.keys():
                tinfo = self.typeinfo(ix)
                self.typeinfo_names[tinfo.tname] = tinfo
            for ix in self.compinfo_table.keys():
                cinfo = self.compinfo(ix)
                self.compinfo_keys[cinfo.ckey] = cinfo

    # ------------------ Printing ----------------------------------------------

    def typ_table_to_string(self) -> str:
        lines: List[str] = []

        def f(ix: int, v: IT.IndexedTableValue) -> None:
            ty = self.typ(ix)
            if ty.is_typedef:
                ty = cast(BCTypNamed, ty)
                resolves = ""
                if ty.typedef is not None:
                    resolves = " (resolves to " + str(ty.typedef.ttype) + ")"
                lines.append(str(ix) + ": " + ty.tname + resolves)
            else:
                lines.append(str(ix) + ": " + str(self.typ(ix)))

        self.typ_table.iter(f)
        return "\n".join(lines)

    def compinfo_table_to_string(self) -> str:
        lines: List[str] = []

        def f(ix: int, v: IT.IndexedTableValue) -> None:
            lines.append(str(ix) + ": " + str(self.compinfo(ix)))

        self.compinfo_table.iter(f)
        return "\n".join(lines)
