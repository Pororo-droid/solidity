/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0
/**
 * @date 2017
 * Converts the AST into json format
 */

#include <libsolidity/ast/ASTJsonExporter.h>

#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/TypeProvider.h>

#include <libyul/AST.h>
#include <libyul/AsmJsonConverter.h>
#include <libyul/backends/evm/EVMDialect.h>

#include <libsolutil/CommonData.h>
#include <libsolutil/JSON.h>
#include <libsolutil/Keccak256.h>
#include <libsolutil/UTF8.h>
#include <libsolutil/Visitor.h>

#include <boost/algorithm/string/join.hpp>

#include <algorithm>
#include <limits>
#include <range/v3/view/map.hpp>
#include <type_traits>
#include <utility>
#include <vector>
#include <filesystem>
// pororo
#include <map>
#include <set>
#include <string>

using namespace std::string_literals;
using namespace solidity::langutil;

namespace
{

template<typename V, template<typename> typename C>
void addIfSet(
	std::vector<std::pair<std::string, Json::Value>>& _attributes, std::string const& _name, C<V> const& _value)
{
	if constexpr (std::is_same_v<C<V>, solidity::util::SetOnce<V>>)
	{
		if (!_value.set())
			return;
	}
	else if constexpr (std::is_same_v<C<V>, std::optional<V>>)
	{
		if (!_value.has_value())
			return;
	}

	_attributes.emplace_back(_name, *_value);
}

}

namespace solidity::frontend
{

ASTJsonExporter::ASTJsonExporter(CompilerStack::State _stackState, std::map<std::string, unsigned> _sourceIndices)
	: m_stackState(_stackState), m_sourceIndices(std::move(_sourceIndices))
{
}


void ASTJsonExporter::setJsonNode(
	ASTNode const& _node,
	std::string const& _nodeName,
	std::initializer_list<std::pair<std::string, Json::Value>>&& _attributes)
{
	ASTJsonExporter::
		setJsonNode(_node, _nodeName, std::vector<std::pair<std::string, Json::Value>>(std::move(_attributes)));
}

void ASTJsonExporter::setJsonNode(
	ASTNode const& _node, std::string const& _nodeType, std::vector<std::pair<std::string, Json::Value>>&& _attributes)
{
	m_currentValue = Json::objectValue;
	m_currentValue["id"] = nodeId(_node);
	m_currentValue["src"] = sourceLocationToString(_node.location());
	if (auto const* documented = dynamic_cast<Documented const*>(&_node))
		if (documented->documentation())
			m_currentValue["documentation"] = *documented->documentation();
	m_currentValue["nodeType"] = _nodeType;
	for (auto& e: _attributes)
		m_currentValue[e.first] = std::move(e.second);
}

std::optional<size_t> ASTJsonExporter::sourceIndexFromLocation(SourceLocation const& _location) const
{
	if (_location.sourceName && m_sourceIndices.count(*_location.sourceName))
		return m_sourceIndices.at(*_location.sourceName);
	else
		return std::nullopt;
}

std::string ASTJsonExporter::sourceLocationToString(SourceLocation const& _location) const
{
	std::optional<size_t> sourceIndexOpt = sourceIndexFromLocation(_location);
	int length = -1;
	if (_location.start >= 0 && _location.end >= 0)
		length = _location.end - _location.start;
	return std::to_string(_location.start) + ":" + std::to_string(length) + ":"
		   + (sourceIndexOpt.has_value() ? std::to_string(sourceIndexOpt.value()) : "-1");
}

Json::Value ASTJsonExporter::sourceLocationsToJson(std::vector<SourceLocation> const& _sourceLocations) const
{
	Json::Value locations = Json::arrayValue;

	for (SourceLocation const& location: _sourceLocations)
		locations.append(sourceLocationToString(location));

	return locations;
}

std::string ASTJsonExporter::namePathToString(std::vector<ASTString> const& _namePath)
{
	return boost::algorithm::join(_namePath, "."s);
}

Json::Value ASTJsonExporter::typePointerToJson(Type const* _tp, bool _withoutDataLocation)
{
	Json::Value typeDescriptions(Json::objectValue);
	typeDescriptions["typeString"] = _tp ? Json::Value(_tp->toString(_withoutDataLocation)) : Json::nullValue;
	typeDescriptions["typeIdentifier"] = _tp ? Json::Value(_tp->identifier()) : Json::nullValue;
	return typeDescriptions;
}
Json::Value ASTJsonExporter::typePointerToJson(std::optional<FuncCallArguments> const& _tps)
{
	if (_tps)
	{
		Json::Value arguments(Json::arrayValue);
		for (auto const& tp: _tps->types)
			appendMove(arguments, typePointerToJson(tp));
		return arguments;
	}
	else
		return Json::nullValue;
}

void ASTJsonExporter::appendExpressionAttributes(
	std::vector<std::pair<std::string, Json::Value>>& _attributes, ExpressionAnnotation const& _annotation)
{
	std::vector<std::pair<std::string, Json::Value>> exprAttributes
		= {std::make_pair("typeDescriptions", typePointerToJson(_annotation.type)),
		   std::make_pair("argumentTypes", typePointerToJson(_annotation.arguments))};

	addIfSet(exprAttributes, "isLValue", _annotation.isLValue);
	addIfSet(exprAttributes, "isPure", _annotation.isPure);
	addIfSet(exprAttributes, "isConstant", _annotation.isConstant);

	if (m_stackState > CompilerStack::State::ParsedAndImported)
		exprAttributes.emplace_back("lValueRequested", _annotation.willBeWrittenTo);

	_attributes += exprAttributes;
}

Json::Value ASTJsonExporter::inlineAssemblyIdentifierToJson(
	std::pair<yul::Identifier const*, InlineAssemblyAnnotation::ExternalIdentifierInfo> _info) const
{
	Json::Value tuple(Json::objectValue);
	tuple["src"] = sourceLocationToString(nativeLocationOf(*_info.first));
	tuple["declaration"] = idOrNull(_info.second.declaration);
	tuple["isSlot"] = Json::Value(_info.second.suffix == "slot");
	tuple["isOffset"] = Json::Value(_info.second.suffix == "offset");

	if (!_info.second.suffix.empty())
		tuple["suffix"] = Json::Value(_info.second.suffix);

	tuple["valueSize"] = Json::Value(Json::LargestUInt(_info.second.valueSize));

	return tuple;
}

// added by pororo
void ASTJsonExporter::findAllReferencedDeclarations(const Json::Value json_value, std::vector<Json::String>& allReferencedDeclarations)
{
	Json::Value::Members members;
	try 
	{
		members = json_value.getMemberNames();
	} catch (const std::exception& e) 
	{
		return;
	}

	for (auto const& member: members)
	{
		if (member == "nodeType" && json_value["nodeType"] == "FunctionDefinition")
		{
			Json::String flag = "|";
			allReferencedDeclarations.push_back(flag);
			if (json_value["name"].asString() != "")	allReferencedDeclarations.push_back(json_value["name"].asString());
			else allReferencedDeclarations.push_back(json_value["kind"].asString());
		}
	}

	for (auto const& member: members)
	{
		if (member == "referencedDeclaration")
		{
			Json::String value = json_value[member].asString();	
			allReferencedDeclarations.push_back(value);
			return;
		}
		if (json_value[member].size() == 0)
			continue;
		
		findAllReferencedDeclarations(json_value[member], allReferencedDeclarations);
		for(auto const& node: json_value[member]) {
			findAllReferencedDeclarations(node, allReferencedDeclarations);
		}
	}
}

void ASTJsonExporter::parseReferencedDeclaration(std::vector<Json::String> allReferencedDeclarations, std::map<Json::Value::Int, Json::String> variableMap)
{
	std::vector<Json::Value::Int> dup_arr;
	bool start = true;
	for(auto const& t: allReferencedDeclarations) 
	{
		if(t == "|")
		{
			start = true;
			std::cout << std::endl;
			continue;
		}
		if(start)
		{
			std::cout << "function: " << t << " uses global variable: ";
			start = false;
			dup_arr.clear();
			continue;
		}
		auto item = variableMap.find(stoi(t));
		bool is_dup = false;
		if (item != variableMap.end())
		{
			for(auto const& d: dup_arr)
			{
				if(d == item->first)
				{
					is_dup = true;
					break;
				}
			}
			if(!is_dup)
			{
				std::cout << item->second << " ";
				dup_arr.push_back(item->first);
			}
		} else if (t == "-15")
		{
			for(auto const& d: dup_arr)
			{
				if(d == -15)
				{
					is_dup = true;
					break;
				}
			}
			if(!is_dup)
			{
				std::cout << "msg.sender ";
				dup_arr.push_back(-15);
			}
		}
	}
}

void ASTJsonExporter::handleHandSide(const Json::Value json_value) {
	if (json_value["nodeType"] == "IndexAccess") {
		// base expression
		std::cout << json_value["baseExpression"]["referencedDeclaration"] << " ";

		// index expression -> [warning] this goes again on expression....
		std::cout << "[";
		handleExpression(json_value["indexExpression"]["expression"]);
		std::cout << "]";
		if (json_value["indexExpression"]["nodeType"] == "MemberAccess") {
			std::cout << "." << json_value["indexExpression"]["memberName"] << " ";	
		}
	} else if (json_value["nodeType"] == "Identifier") {
		// go straight to referencedDeclaration
		std::cout << json_value["referencedDeclaration"] << " ";
	} else if (json_value["nodeType"] == "MemberAccess") {
		handleExpression(json_value["expression"]);
		std::cout << "." << json_value["memberName"] << " ";
	}
}

void ASTJsonExporter::handleExpression(const Json::Value json_value) {
	if (json_value["nodeType"] == "Identifier") {
		std::cout << json_value["referencedDeclaration"] << " ";
	}
	Json::Value leftHandSide, rightHandSide;
	
	// maybe write statement
	leftHandSide = json_value["leftHandSide"];
	handleHandSide(leftHandSide);

	// maybe read statement but becareful with unary operations
	rightHandSide = json_value["rightHandSide"];
	handleHandSide(rightHandSide);

}

Json::Value ASTJsonExporter::findFirstName(const Json::Value json_value)
{
	Json::Value::Members members;
	try 
	{
		members = json_value.getMemberNames();
	} catch (const std::exception& e) 
	{
		return json_value;
	}
	for (auto const& member: members)
	{
		if (member == "name")
		{
			return json_value[member];
		}
	}

	for (auto const& member: members){
		if (json_value[member].size() == 0)
			continue;
		else if(json_value[member].isArray())
		{
			for(auto const& node: json_value[member]) {
				return findFirstName(node);
			}
		}
		else
		{
			return findFirstName(json_value[member]);
		}
	}
	return Json::Value("");
}

std::vector<std::pair<Json::Value, Json::Value>> ASTJsonExporter::findReferenceSet(const Json::Value json_value, std::vector<Json::Value> stateVariables)
{
	std::vector<std::pair<Json::Value, Json::Value>> referenceSet;
	Json::Value::Members members;
	try 
	{
		members = json_value.getMemberNames();
	} catch (const std::exception& e) 
	{
		return referenceSet;
	}
	for (auto const& member: members)
	{
		if (member == "nodeType" && json_value["nodeType"] == "VariableDeclarationStatement")
		{
			for(auto const& declaration: json_value["declarations"])
			{
				if(declaration["storageLocation"] == "storage")
				{
					if(json_value["initialValue"])
						referenceSet.push_back(std::make_pair(declaration["name"], findFirstName(json_value["initialValue"])));
					else
						referenceSet.push_back(std::make_pair(declaration["name"], Json::Value("")));
				}			
			}
		}
		if (json_value[member].size() == 0)
			continue;
		else if(json_value[member].isArray())
		{
			for(auto const& node: json_value[member])
			{
				for(auto const& name: findReferenceSet(node, stateVariables))
					referenceSet.push_back(name);
			}
		}
		else
		{
			for(auto const& name: findReferenceSet(json_value[member], stateVariables))
				referenceSet.push_back(name);
		}
	}
	return referenceSet;
}

Json::Value ASTJsonExporter::findReferenceSet2(const Json::Value json_value, const Json::Value target, std::vector<Json::Value> stateVariables)
{
	Json::Value::Members members;
	try 
	{
		members = json_value.getMemberNames();
	} catch (const std::exception& e) 
	{
		return Json::Value("");
	}
	for (auto const& member: members)
	{
		if (member == "nodeType" && json_value["nodeType"] == "Assignment")
		{
			Json::Value leftHandSide = findFirstName(json_value["leftHandSide"]);
			Json::Value rightHandSide = findFirstName(json_value["rightHandSide"]);
			if(leftHandSide == target && std::find(stateVariables.begin(), stateVariables.end(), rightHandSide) != stateVariables.end())
				return rightHandSide;
		}
		
		if (json_value[member].size() == 0)
			continue;
		else if(json_value[member].isArray())
		{
			for(auto const& node: json_value[member])
			{
				Json::Value result= findReferenceSet2(node, target, stateVariables);
				if(result != "")
					return result;
			}
		}
		else
		{
			Json::Value result = findReferenceSet2(json_value[member], target, stateVariables);
			if(result != "")
				return result;
		}	
	}
	return Json::Value("");
}

std::vector<Json::Value> ASTJsonExporter::deleteFalseRead(std::vector<Json::Value> res)
{
	std::vector<Json::Value> writeSet;
	for(auto const& node: res)
	{
		if(node["type"] == "write")
			writeSet.push_back(node);
	}
	for(auto const& writeNode: writeSet)
	{
		for(auto &node: res)
		{
			if(node["type"] == "read" && node["name"] == writeNode["name"])
			{
				res.erase(std::find(res.begin(), res.end(), node));
				break;
			}
		}
	}
	return res;
}

std::vector<Json::Value> ASTJsonExporter::deleteDuplicate(std::vector<Json::Value> res)
{
	std::vector<Json::Value> newRes;
	for(auto const& node: res)
	{
		if(std::find(newRes.begin(), newRes.end(), node) == newRes.end())
			newRes.push_back(node);
	}
	return newRes;
}

std::vector<Json::Value> ASTJsonExporter::orderingExternalRweSet(std::string funcName, std::vector<std::string> modifierSet, std::map<std::string, std::vector<Json::Value>> externalRweSets, long unsigned int idx)
{
	std::vector<Json::Value> orderedExternalRweSet;
	if(idx >= modifierSet.size())
		return externalRweSets[funcName];
	
	for(auto const& element: externalRweSets[modifierSet[idx]])
	{
		if(element["type"] != "placeholder")
			orderedExternalRweSet.push_back(element);
		else
		{
			auto const& res = orderingExternalRweSet(funcName, modifierSet, externalRweSets, idx+1);
			orderedExternalRweSet.insert(orderedExternalRweSet.end(), res.begin(), res.end());
		}
	}
	return orderedExternalRweSet;
}

std::string ASTJsonExporter::findFullFunctionName(const Json::Value json_value)
{
	std::string functionName = json_value["name"].asString();
	functionName += "(";
	for(auto const& jsonValue: json_value["parameters"]["parameters"]) {
		functionName += jsonValue["typeDescriptions"]["typeString"].asString();
		if(jsonValue["storageLocation"].asString() != "default")
			functionName += " " + jsonValue["storageLocation"].asString();
		functionName += ",";
	}
	if(json_value["parameters"]["parameters"].size() > 0)
		functionName.pop_back();
	functionName += ")";
	return functionName;
}

std::vector<Json::Value> ASTJsonExporter::mergeExternalRweSet(std::string baseFunction, std::map<std::string, std::vector<Json::Value>> externalRweSets)
{
	std::vector<Json::Value> externalRweSet;
	for(auto const& element: externalRweSets[baseFunction])
	{
		if(element["type"] == "internalExecute")
		{
			std::vector<Json::Value> res = mergeExternalRweSet(element["name"].asString(), externalRweSets);
			externalRweSet.insert(externalRweSet.end(), res.begin(), res.end());
		}
		else
			externalRweSet.push_back(element);
	}
	return externalRweSet;
}

std::vector<Json::Value> ASTJsonExporter::mergeExecuteSet(std::vector<std::string> mergedFunctions, std::vector<std::string> mergingFunctions, std::map<std::string, std::vector<Json::Value>> rweSets)
{
	std::vector<Json::Value> rweSet;
	for(auto const& functionName: mergingFunctions)
	{
		if(std::find(mergedFunctions.begin(), mergedFunctions.end(), functionName) == mergedFunctions.end())
		{
			std::vector<std::string> executeSet;
			mergedFunctions.push_back(functionName);
			for(auto const& element: rweSets[functionName])
			{
				if(element["type"] == "execute")
				{
					executeSet.push_back(element["name"].asString());
				}
				rweSet.push_back(element);
			}
			std::vector<Json::Value> res = mergeExecuteSet(mergedFunctions, executeSet, rweSets);
			rweSet.insert(rweSet.end(), res.begin(), res.end());
		}
	}
	return rweSet;
}

std::pair<std::vector<Json::Value>, std::vector<Json::Value>> ASTJsonExporter::findReadWriteSet(const Json::Value json_value, std::vector<Json::Value> stateVariables, std::vector<std::string> declaredFunctions)
{
	std::vector<Json::Value> rweSet;
	std::vector<Json::Value> externalRweSet;
	Json::Value::Members members;
	try 
	{
		members = json_value.getMemberNames();
	} catch (const std::exception& e) 
	{
		return std::make_pair(rweSet, externalRweSet);
	}
	for (auto const& member: members)
	{
		if (member == "nodeType" && json_value["nodeType"] == "Assignment")
		{
			Json::Value leftHandSide = findFirstName(json_value["leftHandSide"]);
			Json::Value rightHandSide = findFirstName(json_value["rightHandSide"]);
			// (a, b , c) = (1, 2, 3)
			if(json_value["leftHandSide"]["components"].size() > 0){
				for(auto const& component: json_value["leftHandSide"]["components"])
				{
					Json::Value componentName = findFirstName(component);
					if(std::find(stateVariables.begin(), stateVariables.end(), componentName) != stateVariables.end())
					{
						Json::Value res(Json::objectValue);
						res["type"] = "write";
						res["name"] = componentName.asString();
						rweSet.push_back(res);
					}
				}
			}
			else{
				if(std::find(stateVariables.begin(), stateVariables.end(), leftHandSide) != stateVariables.end())
				{
					Json::Value res(Json::objectValue);
					res["type"] = "write";
					res["name"] = leftHandSide.asString();
					rweSet.push_back(res);
				}
			}
		}
		else if (member == "nodeType" && json_value["nodeType"] == "UnaryOperation" && (json_value["operator"] == "delete" || json_value["operator"] == "++" || json_value["operator"] == "--"))
		{
			Json::Value unaryExpression = findFirstName(json_value["subExpression"]);
			if(std::find(stateVariables.begin(), stateVariables.end(), unaryExpression) != stateVariables.end())
			{
				Json::Value res(Json::objectValue);
				res["type"] = "write";
				res["name"] = unaryExpression.asString();
				rweSet.push_back(res);
			}
		}
		else if (member == "nodeType" && json_value["nodeType"]== "MemberAccess")
		{
			if(json_value["memberName"] == "push" || json_value["memberName"] == "pop")
			{
				if(std::find(stateVariables.begin(), stateVariables.end(), json_value["expression"]["name"]) != stateVariables.end())
				{
					Json::Value res(Json::objectValue);
					res["type"] = "write";
					res["name"] = json_value["expression"]["name"].asString();
					rweSet.push_back(res);
				}
			}
			else if(json_value["expression"]["referencedDeclaration"] && json_value["expression"]["referencedDeclaration"] < 0)
			{
				if(json_value["memberName"] == "coinbase")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "block.coinbase";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "timestamp")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "block.timestamp";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "difficulty" || json_value["memberName"] == "prevrandao")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "block.prevrandao";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "number")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "block.number";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "gaslimit")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "block.gaslimit";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "sender")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "msg.sender";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "value")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "msg.value";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "origin")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "tx.origin";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "gasprice")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "tx.gasprice";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "chainid")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "block.chainid";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "basefee")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "block.basefee";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "data")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "msg.data";
					rweSet.push_back(res);
				}
				else if(json_value["memberName"] == "sig")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "read";
					res["name"] = "msg.sig";
					rweSet.push_back(res);
				}
			}
			else if(json_value["expression"]["typeDescriptions"]["typeString"].asString().find("address") != std::string::npos)
			{
				if(json_value["memberName"] == "transfer" || json_value["memberName"] == "send")
				{
					Json::Value res(Json::objectValue);
					res["type"] = "execute";
					res["name"] = "";
					externalRweSet.push_back(res);
				}
				else
				{
					if(json_value["memberName"] == "balance")
					{
						Json::Value res(Json::objectValue);
						res["type"] = "read";
						res["name"] = "balance";
						externalRweSet.push_back(res);
					}
					else if(json_value["memberName"] == "code")
					{
						Json::Value res(Json::objectValue);
						res["type"] = "read";
						res["name"] = "code";
						externalRweSet.push_back(res);
					}
					else if(json_value["memberName"] == "codehash")
					{
						Json::Value res(Json::objectValue);
						res["type"] = "read";
						res["name"] = "codehash";
						externalRweSet.push_back(res);
					}
				}
			}
		}
		else if (member == "nodeType" && json_value["nodeType"] == "Identifier")
		{
			if(std::find(stateVariables.begin(), stateVariables.end(), json_value["name"]) != stateVariables.end())
			{
				Json::Value res(Json::objectValue);
				res["type"] = "read";
				res["name"] = json_value["name"].asString();
				rweSet.push_back(res);
			}
		}

		if (member == "nodeType" && json_value["nodeType"] == "FunctionCall")
		{
			std::string functionName = json_value["expression"]["name"].asString();
			std::string functionType = json_value["expression"]["typeDescriptions"]["typeString"].asString();
			functionType = functionType.substr(functionType.find("("), functionType.find(")") - functionType.find("(") + 1);
			functionName += functionType;
			if(std::find(declaredFunctions.begin(), declaredFunctions.end(), functionName) != declaredFunctions.end())
			{
				Json::Value res(Json::objectValue);
				res["type"] = "execute";
				res["name"] = functionName;
				rweSet.push_back(res);
				res["type"] = "internalExecute";
				externalRweSet.push_back(res);
			}
			// Make function that find keyword inside node to simplify
			else if(json_value["expression"]["memberName"] == "call" || json_value["expression"]["memberName"] == "staticcall")
			{
				if(json_value["expression"]["expression"]["typeDescriptions"]["typeString"].asString().find("address") != std::string::npos)
				{
					Json::Value res(Json::objectValue);
					res["type"] = "execute";
					res["name"] = json_value["arguments"][0]["arguments"][0]["value"].asString();
					externalRweSet.push_back(res);
				}
			}
			else if(json_value["expression"]["expression"]["memberName"] == "call" || json_value["expression"]["expression"]["memberName"] == "staticcall")
			{
				if(json_value["expression"]["expression"]["expression"]["typeDescriptions"]["typeString"].asString().find("address") != std::string::npos)
				{
					Json::Value res(Json::objectValue);
					res["type"] = "execute";
					res["name"] = json_value["arguments"][0]["arguments"][0]["value"].asString();
					externalRweSet.push_back(res);
				}
			}
		}

		if(member == "nodeType" && json_value["nodeType"] == "PlaceholderStatement")
		{
			Json::Value res(Json::objectValue);
			res["type"] = "placeholder";
			externalRweSet.push_back(res);
		}

		if (json_value[member].size() == 0)
			continue;
		else if(json_value[member].isArray())
		{
			for(auto const& node: json_value[member])
			{
				auto const& res = findReadWriteSet(node, stateVariables, declaredFunctions);
				for(auto const& element: res.first)
					rweSet.push_back(element);
				for(auto const& element: res.second)
					externalRweSet.push_back(element);
			}
		}
		else
		{
			auto const& res = findReadWriteSet(json_value[member], stateVariables, declaredFunctions);
			for(auto const& element: res.first)
				rweSet.push_back(element);
			for(auto const& element: res.second)
				externalRweSet.push_back(element);
		}
	}
	return std::make_pair(rweSet, externalRweSet);
}

Json::Value ASTJsonExporter::extractRweSet(const Json::Value json_value)
{
	std::vector<Json::Value> stateVariables;
	std::vector<std::string> declaredFunctions;
	std::vector<FunctionName> declaredFunctionSelectors;
	std::map<std::string, std::set<std::pair<Json::Value, Json::Value>>> refSet;
	std::map<std::string, std::vector<Json::Value>> rweSet;
	std::map<std::string, std::vector<Json::Value>> externalRweSet;
	std::map<std::string, std::vector<std::string>> modifierSet;
	Json::Value contractRweSet; 

	// find state variables, function names, and address parameter
	for (auto const& node: json_value["nodes"][1]["nodes"]) {
		if (node["nodeType"] == "VariableDeclaration" && node["stateVariable"] == true && node["mutability"] != "immutable" && node["constant"] == false) {
			stateVariables.push_back(node["name"]);
		}
		if (node["nodeType"] == "FunctionDefinition") {
			FunctionName funcName;
			if(node["kind"] == "fallback" || node["kind"] == "receive"){
				declaredFunctions.push_back(node["kind"].asString());
				funcName.name = node["kind"].asString();
				funcName.functionSelector = "";
				declaredFunctionSelectors.push_back(funcName);
			}
			else{
				declaredFunctions.push_back(findFullFunctionName(node));
				funcName.name = findFullFunctionName(node);
				funcName.functionSelector = node["functionSelector"].asString();
				declaredFunctionSelectors.push_back(funcName);
			}
		}
	}
	
	// find storage reference variables
	for (auto const& node: json_value["nodes"][1]["nodes"]) {
		if (node["nodeType"] == "FunctionDefinition" || node["nodeType"] == "ModifierDefinition"){
			std::string functionName;
			if(node["nodeType"] == "FunctionDefinition")
				functionName = findFullFunctionName(node);
			else
				functionName = node["name"].asString();
			for(auto const& jsonValue: node["body"]["statements"]) {
				for(auto const& name: findReferenceSet(jsonValue, stateVariables)) {
					if(node["kind"] == "fallback") 
						refSet["fallback"].insert(name);
					else if(node["kind"] == "receive")
						refSet["receive"].insert(name);
					else
						refSet[functionName].insert(name);
				}
			}
		}
	}

	// find complete storage reference variables
	for (auto const& node: json_value["nodes"][1]["nodes"]) {
		if (node["nodeType"] == "FunctionDefinition"|| node["nodeType"] == "ModifierDefinition"){
			std::string functionName;
			if(node["nodeType"] == "FunctionDefinition")
				functionName = findFullFunctionName(node);
			else
				functionName = node["name"].asString();
			for(auto const& jsonValue: node["body"]["statements"]) {
				if(node["kind"] == "fallback"){
					for(auto [name, value]: refSet["fallback"]){
						if(value == ""){
							refSet["fallback"].erase(std::make_pair(name, value));
							refSet["fallback"].insert(std::make_pair(name, findReferenceSet2(jsonValue, name, stateVariables)));
						}
					}
				}
				else if(node["kind"] == "receive"){
					for(auto [name, value]: refSet["receive"]){
						if(value == ""){
							refSet["receive"].erase(std::make_pair(name, value));
							refSet["receive"].insert(std::make_pair(name, findReferenceSet2(jsonValue, name, stateVariables)));
						}
					}
				}
				else {
					for(auto [name, value]: refSet[functionName]){
						if(value == ""){
							refSet[functionName].erase(std::make_pair(name, value));
							refSet[functionName].insert(std::make_pair(name, findReferenceSet2(jsonValue, name, stateVariables)));
						}
					}
				}
			}
		}
	}

	// find write set
	for (auto const& node: json_value["nodes"][1]["nodes"])
	{
		if (node["nodeType"] == "FunctionDefinition" || node["nodeType"] == "ModifierDefinition")
		{
			std::string functionName;
			if(node["nodeType"] == "FunctionDefinition")
				functionName = findFullFunctionName(node);
			else
				functionName = node["name"].asString();
			for(auto const& jsonValue: node["body"]["statements"])
			{
				if(node["kind"] == "fallback")
				{
					auto [res, externalRes] = findReadWriteSet(jsonValue, stateVariables, declaredFunctions);
					res = deleteFalseRead(res);
					rweSet["fallback"].insert(rweSet["fallback"].end(), res.begin(), res.end());
					externalRweSet["fallback"].insert(externalRweSet["fallback"].end(), externalRes.begin(), externalRes.end());
					for(auto const& refName: refSet["fallback"])
					{
						Json::Value reference;
						reference["type"] = "read";
						reference["name"] = refName.second.asString();
						rweSet["fallback"].push_back(reference);
						reference["type"] = "write";
						rweSet["fallback"].push_back(reference);
					}
				}
				else if(node["kind"] == "receive")
				{
					auto [res, externalRes] = findReadWriteSet(jsonValue, stateVariables, declaredFunctions);
					res = deleteFalseRead(res);
					rweSet["receive"].insert(rweSet["receive"].end(), res.begin(), res.end());
					externalRweSet["receive"].insert(externalRweSet["receive"].end(), externalRes.begin(), externalRes.end());
					for(auto const& refName: refSet["receive"])
					{
						Json::Value reference;
						reference["type"] = "read";
						reference["name"] = refName.second.asString();
						rweSet["receive"].push_back(reference);
						reference["type"] = "write";
						rweSet["receive"].push_back(reference);
					}
				}
				else
				{	
					auto [res, externalRes] = findReadWriteSet(jsonValue, stateVariables, declaredFunctions);
					res = deleteFalseRead(res);
					rweSet[functionName].insert(rweSet[functionName].end(), res.begin(), res.end());
					externalRweSet[functionName].insert(externalRweSet[functionName].end(), externalRes.begin(), externalRes.end());
					for(auto const& refName: refSet[functionName])
					{
						Json::Value reference;
						reference["type"] = "read";
						reference["name"] = refName.second.asString();
						rweSet[functionName].push_back(reference);
						reference["type"] = "write";
						rweSet[functionName].push_back(reference);
					}
				}
			}
		}

		if(node["nodeType"] == "FunctionDefinition")
		{
			for(auto const& jsonValue: node["modifiers"]) 
				modifierSet[findFullFunctionName(node)].push_back(jsonValue["modifierName"]["name"].asString());
		}
	}
	

	for(auto const& functionName: declaredFunctions)
	{
		std::vector<Json::Value> set = rweSet[functionName];
		for(auto const& modifierName: modifierSet[functionName])
			set.insert(set.end(), rweSet[modifierName].begin(), rweSet[modifierName].end());
		rweSet[functionName] = deleteDuplicate(set);
		externalRweSet[functionName] = orderingExternalRweSet(functionName, modifierSet[functionName], externalRweSet, 0);
	}

	// merge execute set
	for(auto const& functionName: declaredFunctions)
	{
		std::vector<std::string> mergedFunctions(0);
		std::vector<std::string> mergingFunctions;
		for(auto const& element: rweSet[functionName])
		{
			if(element["type"] == "execute")
				mergingFunctions.push_back(element["name"].asString());
		}
		std::vector<Json::Value> res = mergeExecuteSet(mergedFunctions, mergingFunctions, rweSet);
		rweSet[functionName].insert(rweSet[functionName].end(), res.begin(), res.end());
		rweSet[functionName] = deleteDuplicate(rweSet[functionName]);
		externalRweSet[functionName] = mergeExternalRweSet(functionName, externalRweSet);
	}

	for(auto const& functionName: declaredFunctionSelectors)
	{
		std::vector<Json::Value> set = rweSet[functionName.name];
		Json::Value functionRweSet;
		Json::Value exRweSet(Json::arrayValue);
		Json::Value readSet(Json::arrayValue);
		Json::Value writeSet(Json::arrayValue);
		

		functionRweSet["function"] = functionName.name;
		functionRweSet["functionSelector"] = functionName.functionSelector;
		for(auto const& element: set)
		{
			if(element["type"] == "read")
				readSet.append(element["name"]);
			else if(element["type"] == "write")
				writeSet.append(element["name"]);

		}
		functionRweSet["readSet"] = readSet;
		functionRweSet["writeSet"] = writeSet;
		for(auto const& element: externalRweSet[functionName.name])
			exRweSet.append(element);
		functionRweSet["externalRweSet"] = exRweSet;
		contractRweSet.append(functionRweSet);
	}

	// save to json file at ../../rwSet/rwSet.json
	// only if rwSet.json is not exist
	if(!std::filesystem::exists("../../rwSet/rwSet.json"))
	{
		std::ofstream out("../../rwSet/rwSet.json");
		out << contractRweSet;
		out.close();
	}
	
	return contractRweSet;
}

void ASTJsonExporter::printAST(std::ostream& _stream, ASTNode const& _node, util::JsonFormat const& _format)
{
	Json::Value json_value = toJson(_node);
	std::map<Json::Value::Int, Json::String> variable_map;
	// _stream << util::jsonPrint(extractRweSet(json_value), util::JsonFormat{ util::JsonFormat::Pretty }) << std::endl;
	
	for (auto const& node: json_value["nodes"][1]["nodes"])
	{
		if (node["nodeType"] == "VariableDeclaration")
		{
			variable_map.insert(std::make_pair(node["id"].asInt(), node["name"].asString()));
		}
	}
	for (auto iter = variable_map.begin(); iter != variable_map.end(); iter++)
	{
		_stream << iter->first << " " << iter->second << std::endl;
	}
	std::vector<Json::String> allReferencedDeclarations;
	findAllReferencedDeclarations(json_value, allReferencedDeclarations);
	parseReferencedDeclaration(allReferencedDeclarations, variable_map);
	_stream << std::endl;
	_stream << util::jsonPrint(json_value, _format) << std::endl;
	
}
void ASTJsonExporter::print(std::ostream& _stream, ASTNode const& _node, util::JsonFormat const& _format)
{
	_stream << util::jsonPrint(toJson(_node), _format);
}

Json::Value ASTJsonExporter::toJson(ASTNode const& _node)
{
	_node.accept(*this);
	return util::removeNullMembers(std::move(m_currentValue));
}

bool ASTJsonExporter::visit(SourceUnit const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes = {
		std::make_pair("license", _node.licenseString() ? Json::Value(*_node.licenseString()) : Json::nullValue),
		std::make_pair("nodes", toJson(_node.nodes())),
	};

	if (_node.experimentalSolidity())
		attributes.emplace_back("experimentalSolidity", Json::Value(_node.experimentalSolidity()));

	if (_node.annotation().exportedSymbols.set())
	{
		Json::Value exportedSymbols = Json::objectValue;
		for (auto const& sym: *_node.annotation().exportedSymbols)
		{
			exportedSymbols[sym.first] = Json::arrayValue;
			for (Declaration const* overload: sym.second)
				exportedSymbols[sym.first].append(nodeId(*overload));
		}

		attributes.emplace_back("exportedSymbols", exportedSymbols);
	};

	addIfSet(attributes, "absolutePath", _node.annotation().path);

	setJsonNode(_node, "SourceUnit", std::move(attributes));

	return false;
}

bool ASTJsonExporter::visit(PragmaDirective const& _node)
{
	Json::Value literals(Json::arrayValue);
	for (auto const& literal: _node.literals())
		literals.append(literal);
	setJsonNode(_node, "PragmaDirective", {std::make_pair("literals", std::move(literals))});
	return false;
}

bool ASTJsonExporter::visit(ImportDirective const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("file", _node.path()),
		   std::make_pair("sourceUnit", idOrNull(_node.annotation().sourceUnit)),
		   std::make_pair("scope", idOrNull(_node.scope()))};

	addIfSet(attributes, "absolutePath", _node.annotation().absolutePath);

	attributes.emplace_back("unitAlias", _node.name());
	attributes.emplace_back("nameLocation", Json::Value(sourceLocationToString(_node.nameLocation())));

	Json::Value symbolAliases(Json::arrayValue);
	for (auto const& symbolAlias: _node.symbolAliases())
	{
		Json::Value tuple(Json::objectValue);
		solAssert(symbolAlias.symbol, "");
		tuple["foreign"] = toJson(*symbolAlias.symbol);
		tuple["local"] = symbolAlias.alias ? Json::Value(*symbolAlias.alias) : Json::nullValue;
		tuple["nameLocation"] = sourceLocationToString(_node.nameLocation());
		symbolAliases.append(tuple);
	}
	attributes.emplace_back("symbolAliases", std::move(symbolAliases));
	setJsonNode(_node, "ImportDirective", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(ContractDefinition const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("documentation", _node.documentation() ? toJson(*_node.documentation()) : Json::nullValue),
		   std::make_pair("contractKind", contractKind(_node.contractKind())),
		   std::make_pair("abstract", _node.abstract()),
		   std::make_pair("baseContracts", toJson(_node.baseContracts())),
		   std::make_pair(
			   "contractDependencies", getContainerIds(_node.annotation().contractDependencies | ranges::views::keys)),
		   // Do not require call graph because the AST is also created for incorrect sources.
		   std::make_pair("usedEvents", getContainerIds(_node.interfaceEvents(false))),
		   std::make_pair("usedErrors", getContainerIds(_node.interfaceErrors(false))),
		   std::make_pair("nodes", toJson(_node.subNodes())),
		   std::make_pair("scope", idOrNull(_node.scope()))};
	addIfSet(attributes, "canonicalName", _node.annotation().canonicalName);

	if (_node.annotation().unimplementedDeclarations.has_value())
		attributes.emplace_back("fullyImplemented", _node.annotation().unimplementedDeclarations->empty());
	if (!_node.annotation().linearizedBaseContracts.empty())
		attributes.emplace_back("linearizedBaseContracts", getContainerIds(_node.annotation().linearizedBaseContracts));

	if (!_node.annotation().internalFunctionIDs.empty())
	{
		Json::Value internalFunctionIDs(Json::objectValue);
		for (auto const& [functionDefinition, internalFunctionID]: _node.annotation().internalFunctionIDs)
			internalFunctionIDs[std::to_string(functionDefinition->id())] = internalFunctionID;
		attributes.emplace_back("internalFunctionIDs", std::move(internalFunctionIDs));
	}

	setJsonNode(_node, "ContractDefinition", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(IdentifierPath const& _node)
{
	Json::Value nameLocations = Json::arrayValue;

	for (SourceLocation location: _node.pathLocations())
		nameLocations.append(sourceLocationToString(location));

	setJsonNode(
		_node,
		"IdentifierPath",
		{std::make_pair("name", namePathToString(_node.path())),
		 std::make_pair("nameLocations", nameLocations),
		 std::make_pair("referencedDeclaration", idOrNull(_node.annotation().referencedDeclaration))});
	return false;
}

bool ASTJsonExporter::visit(InheritanceSpecifier const& _node)
{
	setJsonNode(
		_node,
		"InheritanceSpecifier",
		{std::make_pair("baseName", toJson(_node.name())),
		 std::make_pair("arguments", _node.arguments() ? toJson(*_node.arguments()) : Json::nullValue)});
	return false;
}

bool ASTJsonExporter::visit(UsingForDirective const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("typeName", _node.typeName() ? toJson(*_node.typeName()) : Json::nullValue)};

	if (_node.usesBraces())
	{
		Json::Value functionList;
		for (auto&& [function, op]: _node.functionsAndOperators())
		{
			Json::Value functionNode;
			if (!op.has_value())
				functionNode["function"] = toJson(*function);
			else
			{
				functionNode["definition"] = toJson(*function);
				functionNode["operator"] = std::string(TokenTraits::toString(*op));
			}
			functionList.append(std::move(functionNode));
		}
		attributes.emplace_back("functionList", std::move(functionList));
	}
	else
	{
		auto const& functionAndOperators = _node.functionsAndOperators();
		solAssert(_node.functionsAndOperators().size() == 1);
		solAssert(!functionAndOperators.front().second.has_value());
		attributes.emplace_back("libraryName", toJson(*(functionAndOperators.front().first)));
	}
	attributes.emplace_back("global", _node.global());

	setJsonNode(_node, "UsingForDirective", std::move(attributes));

	return false;
}

bool ASTJsonExporter::visit(StructDefinition const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("documentation", _node.documentation() ? toJson(*_node.documentation()) : Json::nullValue),
		   std::make_pair("visibility", Declaration::visibilityToString(_node.visibility())),
		   std::make_pair("members", toJson(_node.members())),
		   std::make_pair("scope", idOrNull(_node.scope()))};

	addIfSet(attributes, "canonicalName", _node.annotation().canonicalName);

	setJsonNode(_node, "StructDefinition", std::move(attributes));

	return false;
}

bool ASTJsonExporter::visit(EnumDefinition const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("documentation", _node.documentation() ? toJson(*_node.documentation()) : Json::nullValue),
		   std::make_pair("members", toJson(_node.members()))};

	addIfSet(attributes, "canonicalName", _node.annotation().canonicalName);

	setJsonNode(_node, "EnumDefinition", std::move(attributes));

	return false;
}

bool ASTJsonExporter::visit(EnumValue const& _node)
{
	setJsonNode(
		_node,
		"EnumValue",
		{
			std::make_pair("name", _node.name()),
			std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		});
	return false;
}

bool ASTJsonExporter::visit(UserDefinedValueTypeDefinition const& _node)
{
	solAssert(_node.underlyingType(), "");
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("underlyingType", toJson(*_node.underlyingType()))};
	addIfSet(attributes, "canonicalName", _node.annotation().canonicalName);

	setJsonNode(_node, "UserDefinedValueTypeDefinition", std::move(attributes));

	return false;
}

bool ASTJsonExporter::visit(ParameterList const& _node)
{
	setJsonNode(_node, "ParameterList", {std::make_pair("parameters", toJson(_node.parameters()))});
	return false;
}

bool ASTJsonExporter::visit(OverrideSpecifier const& _node)
{
	setJsonNode(_node, "OverrideSpecifier", {std::make_pair("overrides", toJson(_node.overrides()))});
	return false;
}

bool ASTJsonExporter::visit(FunctionDefinition const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("documentation", _node.documentation() ? toJson(*_node.documentation()) : Json::nullValue),
		   std::make_pair("kind", _node.isFree() ? "freeFunction" : TokenTraits::toString(_node.kind())),
		   std::make_pair("stateMutability", stateMutabilityToString(_node.stateMutability())),
		   std::make_pair("virtual", _node.markedVirtual()),
		   std::make_pair("overrides", _node.overrides() ? toJson(*_node.overrides()) : Json::nullValue),
		   std::make_pair("parameters", toJson(_node.parameterList())),
		   std::make_pair("returnParameters", toJson(*_node.returnParameterList())),
		   std::make_pair("modifiers", toJson(_node.modifiers())),
		   std::make_pair("body", _node.isImplemented() ? toJson(_node.body()) : Json::nullValue),
		   std::make_pair("implemented", _node.isImplemented()),
		   std::make_pair("scope", idOrNull(_node.scope()))};

	std::optional<Visibility> visibility;
	if (_node.isConstructor())
	{
		if (_node.annotation().contract)
			visibility = _node.annotation().contract->abstract() ? Visibility::Internal : Visibility::Public;
	}
	else
		visibility = _node.visibility();

	if (visibility)
		attributes.emplace_back("visibility", Declaration::visibilityToString(*visibility));

	if (_node.isPartOfExternalInterface() && m_stackState > CompilerStack::State::ParsedAndImported)
		attributes.emplace_back("functionSelector", _node.externalIdentifierHex());
	if (!_node.annotation().baseFunctions.empty())
		attributes.emplace_back(
			std::make_pair("baseFunctions", getContainerIds(_node.annotation().baseFunctions, true)));

	setJsonNode(_node, "FunctionDefinition", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(VariableDeclaration const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("typeName", toJson(_node.typeName())),
		   std::make_pair("constant", _node.isConstant()),
		   std::make_pair("mutability", VariableDeclaration::mutabilityToString(_node.mutability())),
		   std::make_pair("stateVariable", _node.isStateVariable()),
		   std::make_pair("storageLocation", location(_node.referenceLocation())),
		   std::make_pair("overrides", _node.overrides() ? toJson(*_node.overrides()) : Json::nullValue),
		   std::make_pair("visibility", Declaration::visibilityToString(_node.visibility())),
		   std::make_pair("value", _node.value() ? toJson(*_node.value()) : Json::nullValue),
		   std::make_pair("scope", idOrNull(_node.scope())),
		   std::make_pair("typeDescriptions", typePointerToJson(_node.annotation().type, true))};
	if (_node.isStateVariable() && _node.isPublic())
		attributes.emplace_back("functionSelector", _node.externalIdentifierHex());
	if (_node.isStateVariable() && _node.documentation())
		attributes.emplace_back("documentation", toJson(*_node.documentation()));
	if (m_inEvent)
		attributes.emplace_back("indexed", _node.isIndexed());
	if (!_node.annotation().baseFunctions.empty())
		attributes.emplace_back(
			std::make_pair("baseFunctions", getContainerIds(_node.annotation().baseFunctions, true)));
	setJsonNode(_node, "VariableDeclaration", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(ModifierDefinition const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("documentation", _node.documentation() ? toJson(*_node.documentation()) : Json::nullValue),
		   std::make_pair("visibility", Declaration::visibilityToString(_node.visibility())),
		   std::make_pair("parameters", toJson(_node.parameterList())),
		   std::make_pair("virtual", _node.markedVirtual()),
		   std::make_pair("overrides", _node.overrides() ? toJson(*_node.overrides()) : Json::nullValue),
		   std::make_pair("body", _node.isImplemented() ? toJson(_node.body()) : Json::nullValue)};
	if (!_node.annotation().baseFunctions.empty())
		attributes.emplace_back(
			std::make_pair("baseModifiers", getContainerIds(_node.annotation().baseFunctions, true)));
	setJsonNode(_node, "ModifierDefinition", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(ModifierInvocation const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes{
		std::make_pair("modifierName", toJson(_node.name())),
		std::make_pair("arguments", _node.arguments() ? toJson(*_node.arguments()) : Json::nullValue)};
	if (Declaration const* declaration = _node.name().annotation().referencedDeclaration)
	{
		if (dynamic_cast<ModifierDefinition const*>(declaration))
			attributes.emplace_back("kind", "modifierInvocation");
		else if (dynamic_cast<ContractDefinition const*>(declaration))
			attributes.emplace_back("kind", "baseConstructorSpecifier");
	}
	setJsonNode(_node, "ModifierInvocation", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(EventDefinition const& _node)
{
	m_inEvent = true;
	std::vector<std::pair<std::string, Json::Value>> _attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("documentation", _node.documentation() ? toJson(*_node.documentation()) : Json::nullValue),
		   std::make_pair("parameters", toJson(_node.parameterList())),
		   std::make_pair("anonymous", _node.isAnonymous())};
	if (m_stackState >= CompilerStack::State::AnalysisSuccessful)
		_attributes.emplace_back(std::make_pair(
			"eventSelector",
			toHex(u256(util::h256::Arith(util::keccak256(_node.functionType(true)->externalSignature()))))));

	setJsonNode(_node, "EventDefinition", std::move(_attributes));
	return false;
}

bool ASTJsonExporter::visit(ErrorDefinition const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> _attributes
		= {std::make_pair("name", _node.name()),
		   std::make_pair("nameLocation", sourceLocationToString(_node.nameLocation())),
		   std::make_pair("documentation", _node.documentation() ? toJson(*_node.documentation()) : Json::nullValue),
		   std::make_pair("parameters", toJson(_node.parameterList()))};
	if (m_stackState >= CompilerStack::State::AnalysisSuccessful)
		_attributes.emplace_back(std::make_pair("errorSelector", _node.functionType(true)->externalIdentifierHex()));

	setJsonNode(_node, "ErrorDefinition", std::move(_attributes));
	return false;
}

bool ASTJsonExporter::visit(ElementaryTypeName const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("name", _node.typeName().toString()),
		   std::make_pair("typeDescriptions", typePointerToJson(_node.annotation().type, true))};

	if (_node.stateMutability())
		attributes.emplace_back(std::make_pair("stateMutability", stateMutabilityToString(*_node.stateMutability())));

	setJsonNode(_node, "ElementaryTypeName", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(UserDefinedTypeName const& _node)
{
	setJsonNode(
		_node,
		"UserDefinedTypeName",
		{std::make_pair("pathNode", toJson(_node.pathNode())),
		 std::make_pair("referencedDeclaration", idOrNull(_node.pathNode().annotation().referencedDeclaration)),
		 std::make_pair("typeDescriptions", typePointerToJson(_node.annotation().type, true))});
	return false;
}

bool ASTJsonExporter::visit(FunctionTypeName const& _node)
{
	setJsonNode(
		_node,
		"FunctionTypeName",
		{std::make_pair("visibility", Declaration::visibilityToString(_node.visibility())),
		 std::make_pair("stateMutability", stateMutabilityToString(_node.stateMutability())),
		 std::make_pair("parameterTypes", toJson(*_node.parameterTypeList())),
		 std::make_pair("returnParameterTypes", toJson(*_node.returnParameterTypeList())),
		 std::make_pair("typeDescriptions", typePointerToJson(_node.annotation().type, true))});
	return false;
}

bool ASTJsonExporter::visit(Mapping const& _node)
{
	setJsonNode(
		_node,
		"Mapping",
		{std::make_pair("keyType", toJson(_node.keyType())),
		 std::make_pair("keyName", _node.keyName()),
		 std::make_pair("keyNameLocation", sourceLocationToString(_node.keyNameLocation())),
		 std::make_pair("valueType", toJson(_node.valueType())),
		 std::make_pair("valueName", _node.valueName()),
		 std::make_pair("valueNameLocation", sourceLocationToString(_node.valueNameLocation())),
		 std::make_pair("typeDescriptions", typePointerToJson(_node.annotation().type, true))});
	return false;
}

bool ASTJsonExporter::visit(ArrayTypeName const& _node)
{
	setJsonNode(
		_node,
		"ArrayTypeName",
		{std::make_pair("baseType", toJson(_node.baseType())),
		 std::make_pair("length", toJsonOrNull(_node.length())),
		 std::make_pair("typeDescriptions", typePointerToJson(_node.annotation().type, true))});
	return false;
}

bool ASTJsonExporter::visit(InlineAssembly const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> externalReferences;

	for (auto const& it: _node.annotation().externalReferences)
		if (it.first)
			externalReferences.emplace_back(std::make_pair(it.first->name.str(), inlineAssemblyIdentifierToJson(it)));

	Json::Value externalReferencesJson = Json::arrayValue;

	std::sort(externalReferences.begin(), externalReferences.end());
	for (Json::Value& it: externalReferences | ranges::views::values)
		externalReferencesJson.append(std::move(it));

	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair(
			   "AST",
			   Json::Value(yul::AsmJsonConverter(sourceIndexFromLocation(_node.location()))(_node.operations()))),
		   std::make_pair("externalReferences", std::move(externalReferencesJson)),
		   std::make_pair(
			   "evmVersion", dynamic_cast<solidity::yul::EVMDialect const&>(_node.dialect()).evmVersion().name())};

	if (_node.flags())
	{
		Json::Value flags(Json::arrayValue);
		for (auto const& flag: *_node.flags())
			if (flag)
				flags.append(*flag);
			else
				flags.append(Json::nullValue);
		attributes.emplace_back(std::make_pair("flags", std::move(flags)));
	}
	setJsonNode(_node, "InlineAssembly", std::move(attributes));

	return false;
}

bool ASTJsonExporter::visit(Block const& _node)
{
	setJsonNode(
		_node,
		_node.unchecked() ? "UncheckedBlock" : "Block",
		{std::make_pair("statements", toJson(_node.statements()))});
	return false;
}

bool ASTJsonExporter::visit(PlaceholderStatement const& _node)
{
	setJsonNode(_node, "PlaceholderStatement", {});
	return false;
}

bool ASTJsonExporter::visit(IfStatement const& _node)
{
	setJsonNode(
		_node,
		"IfStatement",
		{std::make_pair("condition", toJson(_node.condition())),
		 std::make_pair("trueBody", toJson(_node.trueStatement())),
		 std::make_pair("falseBody", toJsonOrNull(_node.falseStatement()))});
	return false;
}

bool ASTJsonExporter::visit(TryCatchClause const& _node)
{
	setJsonNode(
		_node,
		"TryCatchClause",
		{std::make_pair("errorName", _node.errorName()),
		 std::make_pair("parameters", toJsonOrNull(_node.parameters())),
		 std::make_pair("block", toJson(_node.block()))});
	return false;
}

bool ASTJsonExporter::visit(TryStatement const& _node)
{
	setJsonNode(
		_node,
		"TryStatement",
		{std::make_pair("externalCall", toJson(_node.externalCall())),
		 std::make_pair("clauses", toJson(_node.clauses()))});
	return false;
}

bool ASTJsonExporter::visit(WhileStatement const& _node)
{
	setJsonNode(
		_node,
		_node.isDoWhile() ? "DoWhileStatement" : "WhileStatement",
		{std::make_pair("condition", toJson(_node.condition())), std::make_pair("body", toJson(_node.body()))});
	return false;
}

bool ASTJsonExporter::visit(ForStatement const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("initializationExpression", toJsonOrNull(_node.initializationExpression())),
		   std::make_pair("condition", toJsonOrNull(_node.condition())),
		   std::make_pair("loopExpression", toJsonOrNull(_node.loopExpression())),
		   std::make_pair("body", toJson(_node.body()))};

	if (_node.annotation().isSimpleCounterLoop.set())
		attributes.emplace_back("isSimpleCounterLoop", *_node.annotation().isSimpleCounterLoop);

	setJsonNode(_node, "ForStatement", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(Continue const& _node)
{
	setJsonNode(_node, "Continue", {});
	return false;
}

bool ASTJsonExporter::visit(Break const& _node)
{
	setJsonNode(_node, "Break", {});
	return false;
}

bool ASTJsonExporter::visit(Return const& _node)
{
	setJsonNode(
		_node,
		"Return",
		{std::make_pair("expression", toJsonOrNull(_node.expression())),
		 std::make_pair("functionReturnParameters", idOrNull(_node.annotation().functionReturnParameters))});
	return false;
}

bool ASTJsonExporter::visit(Throw const& _node)
{
	setJsonNode(_node, "Throw", {});
	return false;
}

bool ASTJsonExporter::visit(EmitStatement const& _node)
{
	setJsonNode(_node, "EmitStatement", {std::make_pair("eventCall", toJson(_node.eventCall()))});
	return false;
}

bool ASTJsonExporter::visit(RevertStatement const& _node)
{
	setJsonNode(_node, "RevertStatement", {std::make_pair("errorCall", toJson(_node.errorCall()))});
	return false;
}

bool ASTJsonExporter::visit(VariableDeclarationStatement const& _node)
{
	Json::Value varDecs(Json::arrayValue);
	for (auto const& v: _node.declarations())
		appendMove(varDecs, idOrNull(v.get()));
	setJsonNode(
		_node,
		"VariableDeclarationStatement",
		{std::make_pair("assignments", std::move(varDecs)),
		 std::make_pair("declarations", toJson(_node.declarations())),
		 std::make_pair("initialValue", toJsonOrNull(_node.initialValue()))});
	return false;
}

bool ASTJsonExporter::visit(ExpressionStatement const& _node)
{
	setJsonNode(_node, "ExpressionStatement", {std::make_pair("expression", toJson(_node.expression()))});
	return false;
}

bool ASTJsonExporter::visit(Conditional const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("condition", toJson(_node.condition())),
		   std::make_pair("trueExpression", toJson(_node.trueExpression())),
		   std::make_pair("falseExpression", toJson(_node.falseExpression()))};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "Conditional", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(Assignment const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("operator", TokenTraits::toString(_node.assignmentOperator())),
		   std::make_pair("leftHandSide", toJson(_node.leftHandSide())),
		   std::make_pair("rightHandSide", toJson(_node.rightHandSide()))};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "Assignment", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(TupleExpression const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes = {
		std::make_pair("isInlineArray", Json::Value(_node.isInlineArray())),
		std::make_pair("components", toJson(_node.components())),
	};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "TupleExpression", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(UnaryOperation const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("prefix", _node.isPrefixOperation()),
		   std::make_pair("operator", TokenTraits::toString(_node.getOperator())),
		   std::make_pair("subExpression", toJson(_node.subExpression()))};
	// NOTE: This annotation is guaranteed to be set but only if we didn't stop at the parsing stage.
	if (_node.annotation().userDefinedFunction.set() && *_node.annotation().userDefinedFunction != nullptr)
		attributes.emplace_back("function", nodeId(**_node.annotation().userDefinedFunction));
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "UnaryOperation", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(BinaryOperation const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes = {
		std::make_pair("operator", TokenTraits::toString(_node.getOperator())),
		std::make_pair("leftExpression", toJson(_node.leftExpression())),
		std::make_pair("rightExpression", toJson(_node.rightExpression())),
		std::make_pair("commonType", typePointerToJson(_node.annotation().commonType)),
	};
	// NOTE: This annotation is guaranteed to be set but only if we didn't stop at the parsing stage.
	if (_node.annotation().userDefinedFunction.set() && *_node.annotation().userDefinedFunction != nullptr)
		attributes.emplace_back("function", nodeId(**_node.annotation().userDefinedFunction));
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "BinaryOperation", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(FunctionCall const& _node)
{
	Json::Value names(Json::arrayValue);
	for (auto const& name: _node.names())
		names.append(Json::Value(*name));
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("expression", toJson(_node.expression())),
		   std::make_pair("names", std::move(names)),
		   std::make_pair("nameLocations", sourceLocationsToJson(_node.nameLocations())),
		   std::make_pair("arguments", toJson(_node.arguments())),
		   std::make_pair("tryCall", _node.annotation().tryCall)};

	if (_node.annotation().kind.set())
	{
		FunctionCallKind nodeKind = *_node.annotation().kind;
		attributes.emplace_back("kind", functionCallKind(nodeKind));
	}

	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "FunctionCall", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(FunctionCallOptions const& _node)
{
	Json::Value names(Json::arrayValue);
	for (auto const& name: _node.names())
		names.append(Json::Value(*name));

	std::vector<std::pair<std::string, Json::Value>> attributes = {
		std::make_pair("expression", toJson(_node.expression())),
		std::make_pair("names", std::move(names)),
		std::make_pair("options", toJson(_node.options())),
	};
	appendExpressionAttributes(attributes, _node.annotation());

	setJsonNode(_node, "FunctionCallOptions", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(NewExpression const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("typeName", toJson(_node.typeName()))};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "NewExpression", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(MemberAccess const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes = {
		std::make_pair("memberName", _node.memberName()),
		std::make_pair("memberLocation", Json::Value(sourceLocationToString(_node.memberLocation()))),
		std::make_pair("expression", toJson(_node.expression())),
		std::make_pair("referencedDeclaration", idOrNull(_node.annotation().referencedDeclaration)),
	};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "MemberAccess", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(IndexAccess const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes = {
		std::make_pair("baseExpression", toJson(_node.baseExpression())),
		std::make_pair("indexExpression", toJsonOrNull(_node.indexExpression())),
	};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "IndexAccess", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(IndexRangeAccess const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes = {
		std::make_pair("baseExpression", toJson(_node.baseExpression())),
		std::make_pair("startExpression", toJsonOrNull(_node.startExpression())),
		std::make_pair("endExpression", toJsonOrNull(_node.endExpression())),
	};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "IndexRangeAccess", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(Identifier const& _node)
{
	Json::Value overloads(Json::arrayValue);
	for (auto const& dec: _node.annotation().overloadedDeclarations)
		overloads.append(nodeId(*dec));
	
	setJsonNode(
		_node,
		"Identifier",
		{std::make_pair("name", _node.name()),
		 std::make_pair("referencedDeclaration", idOrNull(_node.annotation().referencedDeclaration)),
		 std::make_pair("overloadedDeclarations", overloads),
		 std::make_pair("typeDescriptions", typePointerToJson(_node.annotation().type)),
		 std::make_pair("argumentTypes", typePointerToJson(_node.annotation().arguments))});
	return false;
}

bool ASTJsonExporter::visit(ElementaryTypeNameExpression const& _node)
{
	std::vector<std::pair<std::string, Json::Value>> attributes = {std::make_pair("typeName", toJson(_node.type()))};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "ElementaryTypeNameExpression", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(Literal const& _node)
{
	Json::Value value{_node.value()};
	if (!util::validateUTF8(_node.value()))
		value = Json::nullValue;
	Token subdenomination = Token(_node.subDenomination());
	std::vector<std::pair<std::string, Json::Value>> attributes
		= {std::make_pair("kind", literalTokenKind(_node.token())),
		   std::make_pair("value", value),
		   std::make_pair("hexValue", util::toHex(util::asBytes(_node.value()))),
		   std::make_pair(
			   "subdenomination",
			   subdenomination == Token::Illegal ? Json::nullValue
												 : Json::Value{TokenTraits::toString(subdenomination)})};
	appendExpressionAttributes(attributes, _node.annotation());
	setJsonNode(_node, "Literal", std::move(attributes));
	return false;
}

bool ASTJsonExporter::visit(StructuredDocumentation const& _node)
{
	Json::Value text{*_node.text()};
	std::vector<std::pair<std::string, Json::Value>> attributes = {std::make_pair("text", text)};
	setJsonNode(_node, "StructuredDocumentation", std::move(attributes));
	return false;
}


void ASTJsonExporter::endVisit(EventDefinition const&) { m_inEvent = false; }

bool ASTJsonExporter::visitNode(ASTNode const& _node)
{
	solAssert(
		false,
		_node.experimentalSolidityOnly() ? "Attempt to export an AST of experimental solidity."
										 : "Attempt to export an AST that contains unexpected nodes.");
	return false;
}

std::string ASTJsonExporter::location(VariableDeclaration::Location _location)
{
	switch (_location)
	{
	case VariableDeclaration::Location::Unspecified:
		return "default";
	case VariableDeclaration::Location::Storage:
		return "storage";
	case VariableDeclaration::Location::Memory:
		return "memory";
	case VariableDeclaration::Location::CallData:
		return "calldata";
	}
	// To make the compiler happy
	return {};
}

std::string ASTJsonExporter::contractKind(ContractKind _kind)
{
	switch (_kind)
	{
	case ContractKind::Interface:
		return "interface";
	case ContractKind::Contract:
		return "contract";
	case ContractKind::Library:
		return "library";
	}

	// To make the compiler happy
	return {};
}

std::string ASTJsonExporter::functionCallKind(FunctionCallKind _kind)
{
	switch (_kind)
	{
	case FunctionCallKind::FunctionCall:
		return "functionCall";
	case FunctionCallKind::TypeConversion:
		return "typeConversion";
	case FunctionCallKind::StructConstructorCall:
		return "structConstructorCall";
	default:
		solAssert(false, "Unknown kind of function call.");
	}
}

std::string ASTJsonExporter::literalTokenKind(Token _token)
{
	switch (_token)
	{
	case Token::Number:
		return "number";
	case Token::StringLiteral:
		return "string";
	case Token::UnicodeStringLiteral:
		return "unicodeString";
	case Token::HexStringLiteral:
		return "hexString";
	case Token::TrueLiteral:
	case Token::FalseLiteral:
		return "bool";
	default:
		solAssert(false, "Unknown kind of literal token.");
	}
}

std::string ASTJsonExporter::type(Expression const& _expression)
{
	return _expression.annotation().type ? _expression.annotation().type->toString() : "Unknown";
}

std::string ASTJsonExporter::type(VariableDeclaration const& _varDecl)
{
	return _varDecl.annotation().type ? _varDecl.annotation().type->toString() : "Unknown";
}
}