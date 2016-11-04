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

public class ASTRuntimeException extends RuntimeException {
    private final SourceInfo sourceInfo;

    public ASTRuntimeException(SourceInfo sourceInfo, String message) {
        super(message + description(sourceInfo));
        this.sourceInfo = sourceInfo;
    }

    public ASTRuntimeException(SourceInfo sourceInfo, String message, Throwable throwable) {
        super(message + description(sourceInfo), throwable);
        this.sourceInfo = null;
    }

    protected static String description(SourceInfo node) {
        return (node != null) ? " at line: " + node.getLine() + " column: " + node.getColumn() : "";
    }

    public SourceInfo getSourceInfo() {
        return sourceInfo;
    }

    public int getLine() {
        return sourceInfo != null ? sourceInfo.getLine() : -1;
    }

    public int getColumn() {
        return sourceInfo != null ? sourceInfo.getColumn() : -1;
    }

}
