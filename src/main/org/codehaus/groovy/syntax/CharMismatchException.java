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

package org.codehaus.groovy.syntax;

/**
 * Indicates a parsing failure in the lexer at a certain char
 * optionally offering the expected alternative char.
 */
public class CharMismatchException extends SyntaxException {
    private char badChar;
    private char expectedChar;

    public CharMismatchException(char badChar, char expectedChar, String message, Throwable cause, int startLine, int startColumn, int endLine, int endColumn) {
        super(message, cause, startLine, startColumn, endLine, endColumn);
        this.badChar = badChar;
        this.expectedChar = expectedChar;
    }

    public char getBadChar() {
        return badChar;
    }

    /**
     * returns the expected char or NO_CHAR if not available
     * @see Chars#NO_CHAR
     */
    public char getExpectedChar() {
        return expectedChar;
    }
}
