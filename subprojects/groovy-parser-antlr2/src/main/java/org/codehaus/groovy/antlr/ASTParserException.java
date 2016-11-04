/*
 *  Licensed to the Apache Software Foundation (ASF) under one
 *  or more contributor license agreements.  See the NOTICE file
 *  distributed with this work for additional information
 *  regarding copyright ownership.  The ASF licenses this file
 *  to you under the Apache License, Version 2.0 (the
 *  "License"); you may not use this file except in compliance
 *  with the License.  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing,
 *  software distributed under the License is distributed on an
 *  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 *  KIND, either express or implied.  See the License for the
 *  specific language governing permissions and limitations
 *  under the License.
 */
package org.codehaus.groovy.antlr;

import antlr.collections.AST;
import org.codehaus.groovy.syntax.ParserException;

/**
 * Thrown when trying to parse the AST
 *
 */
public class ASTParserException extends ParserException {

    public ASTParserException(ASTRuntimeException e) {
        super(e.getMessage(), e, e.getLine(), e.getColumn(), getLineLast(e), getColumnLast(e));
    }

    public ASTParserException(String message, ASTRuntimeException e) {
        super(message, e, e.getLine(), e.getColumn(), getLineLast(e), getColumnLast(e));
    }

    public SourceInfo getSourceInfo() {
        return ((ASTRuntimeException) getCause()).getSourceInfo();
    }

    private static int getLineLast(ASTRuntimeException e) {
        final SourceInfo sourceInfo = e.getSourceInfo();
        return (sourceInfo instanceof SourceInfo) ? ((SourceInfo)sourceInfo).getLineLast() : sourceInfo.getLine();
    }

    private static int getColumnLast(ASTRuntimeException e) {
        final SourceInfo ast = e.getSourceInfo();
        return (ast instanceof SourceInfo) ? ((SourceInfo)ast).getColumnLast() : ast.getColumn()+1;
    }
}
