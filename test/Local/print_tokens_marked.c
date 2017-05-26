#include "mark.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tokens.h"

#define START 5
#define TRUE 1
#define FALSE 0

static token numeric_case();
static token error_or_eof_case();
static int check_delimiter();
static int keyword(int state);
static int special(int state);
static void skip(character_stream stream_ptr);
static int constant(int state, char token_str[], int token_ind);
static int next_state();
static void get_actual_token(char token_str[], int token_ind);

int print_token(token token_ptr);

int main(int argc, char *argv[]) {
  MARK(1, 7);
  token token_ptr;
  token_stream stream_ptr;

  if (argc > 2) {
    fprintf(stdout, "The format is print_tokens filename(optional)\n");
    (MARK(1, 6), exit(1));
  }
  stream_ptr = (MARK(1, 5), open_token_stream(argv[1]));

  while (!is_eof_token((token_ptr = (MARK(1, 4), get_token(stream_ptr))))) {
    (mark(1, 3), print_token(token_ptr));
  }
  print_token(token_ptr);
  (MARK(1, 1), exit(0));
}

/* *********************************************************************
       Function name : open_character_stream
       Input         : filename
       Output        : charactre stream.
       Exceptions    : If file name doesn't exists it will
                       exit from the program.
       Description   : The function first allocates the memory for
                       the structure and initilizes it. The constant
                       START gives the first character available in
                       the stream. It ckecks whether the filename is
                       empty string. If it is it assigns file pointer
                       to stdin else it opens the respective file as input.
   * ******************************************************************* */

character_stream open_character_stream(char *FILENAME) {
  MARK(2, 5);
  character_stream stream_ptr;

  stream_ptr = (character_stream)malloc(sizeof(struct stream_type));
  stream_ptr->stream_ind = START;
  stream_ptr->stream[START] = '\0';
  if (FILENAME == NULL) {
    (mark(2, 4), stream_ptr->fp = stdin);
  } else if ((stream_ptr->fp = (mark(2, 3), fopen(FILENAME, "r"))) == NULL) {
    fprintf(stdout, "The file %s doesn't exists\n", FILENAME);
    (MARK(2, 2), exit(0));
  }
  return (MARK(2, 1), (stream_ptr));
}

/* *********************************************************************
   Function name : get_char
   Input         : charcter_stream.
   Output        : character.
   Exceptions    : None.
   Description   : This function takes character_stream type variable
                   as input and returns one character. If the stream is
                   empty then it reads the next line from the file and
                   returns the character.
 * ****************************************************************** */

char get_char(character_stream stream_ptr) {
  if ((MARK(3, 5), stream_ptr->stream[stream_ptr->stream_ind] == '\0')) {
    if ((mark(3, 4),
         fgets(stream_ptr->stream + START, 80 - START, stream_ptr->fp)) ==
        NULL) { /* Fix bug: add -START - hf*/
      (mark(3, 3), stream_ptr->stream[START] = EOF);
    }
    (mark(3, 2), stream_ptr->stream_ind = START);
  }
  char result_4dd07959df = (stream_ptr->stream[(stream_ptr->stream_ind)++]);
  return (MARK(3, 1), (result_4dd07959df));
}

/* *******************************************************************
   Function name : is_end_of_character_stream.
   Input         : character_stream.
   Output        : Boolean value.
   Description   : This function checks whether it is end of character
                   stream or not. It returns BOOLEANvariable which is
                   true or false. The function checks whether the last
                   read character is end file character or not and
                   returns the value according to it.
 * ****************************************************************** */

int is_end_of_character_stream(character_stream stream_ptr) {
  if ((MARK(4, 3), stream_ptr->stream[stream_ptr->stream_ind - 1] == EOF)) {
    return (MARK(4, 2), (TRUE));
  } else {
    return (MARK(4, 1), (FALSE));
  }
}

/* *********************************************************************
   Function name : unget_char
   Input         : character,character_stream.
   Output        : void.
   Description   : This function adds the character ch to the stream.
                   This is accomplished by decrementing the stream_ind
                   and storing it in the stream. If it is not possible
                   to unget the character then it returns
 * ******************************************************************* */

void unget_char(int ch, character_stream stream_ptr) {
  if ((MARK(5, 4), stream_ptr->stream_ind == 0)) {
    MARK(5, 3);
    return;
  } else {
    (mark(5, 2), stream_ptr->stream[--(stream_ptr->stream_ind)] = ch);
  }
  MARK(5, 1);
  return;
}

/* *******************************************************************
   Function name : open_token_stream
   Input         : filename
   Output        : token_stream
   Exceptions    : Exits if the file specified by filename not found.
   Description   : This function takes filename as input and opens the
                   token_stream which is nothing but the character stream.
                   This function allocates the memory for token_stream
                   and calls open_character_stream to open the file as
                   input. This function returns the token_stream.
 * ****************************************************************** */

token_stream open_token_stream(char *FILENAME) {
  MARK(6, 1);
  token_stream token_ptr;

  token_ptr = (token_stream)malloc(sizeof(struct token_stream_type));
  token_ptr->ch_stream = open_character_stream(FILENAME); /* Get character
                                                              stream  */
  return (MARK(6, 13), (token_ptr));
}

/* ********************************************************************
   Function name : get_token
   Input         : token_stream
   Output        : token
   Exceptions    : none.
   Description   : This function returns the next token from the
                   token_stream.The type of token is integer and specifies
                   only the type of the token. DFA is used for finding the
                   next token. cu_state is initialized to zero and charcter
                   are read until the the is the final state and it
                   returns the token type.
* ******************************************************************* */

token get_token(token_stream tstream_ptr) {
  MARK(7, 34);
  char token_str[80]; /* This buffer stores the current token */
  int token_ind;      /* Index to the token_str  */
  token token_ptr;
  char ch;
  int cu_state, next_st, token_found;

  token_ptr = (token)(malloc(sizeof(struct token_type)));
  ch = get_char(tstream_ptr->ch_stream);
  cu_state = token_ind = token_found = 0;
  while ((MARK(7, 33), !token_found)) {
    if ((mark(7, 32), token_ind < 80)) { /* ADDED ERROR CHECK - hf */
      (mark(7, 31), token_str[token_ind++] = ch);
      next_st = next_state(cu_state, ch);
    } else {
      (mark(7, 30), next_st = -1); /* - hf */
    }
    if ((mark(7, 29), next_st == -1)) { /* ERROR or EOF case */
      token result_4882dff095 = (error_or_eof_case(
          tstream_ptr, token_ptr, cu_state, token_str, token_ind, ch));
      return (MARK(7, 28), (result_4882dff095));
    } else if ((mark(7, 27), next_st == -2)) { /* This is numeric case. */
      token result_8025f5e6e0 =
          (numeric_case(tstream_ptr, token_ptr, ch, token_str, token_ind));
      return (MARK(7, 26), (result_8025f5e6e0));
    } else if ((mark(7, 25), next_st == -3)) { /* This is the IDENTIFIER case */
      token_ptr->token_id = IDENTIFIER;
      unget_char(ch, tstream_ptr->ch_stream);
      token_ind--;
      get_actual_token(token_str, token_ind);
      strcpy(token_ptr->token_string, token_str);
      return (MARK(7, 24), (token_ptr));
    }

    switch ((mark(7, 4), next_st)) {
    default:
      break;
    case 6: /* These are all KEYWORD cases. */
    case 9:
    case 11:
    case 13:
    case 16:
      ch = (mark(7, 18), get_char(tstream_ptr->ch_stream));
      if (check_delimiter(ch) == TRUE) {
        token_ptr->token_id = keyword(next_st);
        unget_char(ch, tstream_ptr->ch_stream);
        token_ptr->token_string[0] = '\0';
        return (MARK(7, 17), (token_ptr));
      }
      (mark(7, 16), unget_char(ch, tstream_ptr->ch_stream));
      break;
    case 19: /* These are all special SPECIAL character */
    case 20: /* cases */
    case 21:
    case 22:
    case 23:
    case 24:
    case 25:
    case 32:
      token_ptr->token_id = special(next_st);
      token_ptr->token_string[0] = '\0';
      return (MARK(7, 8), (token_ptr));
    case 27: /* These are constant cases */
    case 29:
      token_ptr->token_id = constant(next_st, token_str, token_ind);
      get_actual_token(token_str, token_ind);
      strcpy(token_ptr->token_string, token_str);
      return (MARK(7, 6), (token_ptr));
    case 30: /* This is COMMENT case */
      (mark(7, 5), skip(tstream_ptr->ch_stream));
      token_ind = next_st = 0;
      break;
    }
    (mark(7, 3), cu_state = next_st);
    ch = get_char(tstream_ptr->ch_stream);
  }
  return (MARK(7, 1), NULL);
}

/* ******************************************************************
   Function name : numeric_case
   Input         : tstream_ptr,token_ptr,ch,token_str,token_ind
   Output        : token_ptr;
   Exceptions    : none
   Description   : It checks for the delimiter, if it is then it
                   forms numeric token else forms error token.
 * ****************************************************************** */

static token numeric_case(token_stream tstream_ptr, token token_ptr, int ch,
                          char token_str[], int token_ind) {
  if ((MARK(8, 9), check_delimiter(ch)) != TRUE) { /* Error case */
    (mark(8, 8), token_ptr->token_id = ERROR);
    while ((MARK(8, 7), check_delimiter(ch)) == FALSE) {
      if ((mark(8, 6), token_ind >= 80)) {
        break; /* Added protection - hf */
      }
      token_str[token_ind++] = ch =
          (mark(8, 4), get_char(tstream_ptr->ch_stream));
    }
    unget_char(ch, tstream_ptr->ch_stream);
    token_ind--;
    get_actual_token(token_str, token_ind);
    strcpy(token_ptr->token_string, token_str);
    return (MARK(8, 2), (token_ptr));
  }
  token_ptr->token_id = NUMERIC; /* Numeric case */
  unget_char(ch, tstream_ptr->ch_stream);
  token_ind--;
  get_actual_token(token_str, token_ind);
  strcpy(token_ptr->token_string, token_str);
  return (MARK(8, 1), (token_ptr));
}

/* *****************************************************************
   Function name : error_or_eof_case
   Input         : tstream_ptr,token_ptr,cu_state,token_str,token_ind,ch
   Output        : token_ptr
   Exceptions    : none
   Description   : This function checks whether it is EOF or not.
                   If it is it returns EOF token else returns ERROR
                   token.
 * *****************************************************************/

static token error_or_eof_case(token_stream tstream_ptr, token token_ptr,
                               int cu_state, char token_str[], int token_ind,
                               int ch) {
  if ((MARK(9, 5), is_end_of_character_stream(tstream_ptr->ch_stream))) {
    token_ptr->token_id = EOTSTREAM;
    token_ptr->token_string[0] = '\0';
    return (MARK(9, 4), (token_ptr));
  }
  if ((mark(9, 3), cu_state != 0)) {
    (mark(9, 2), unget_char(ch, tstream_ptr->ch_stream));
    token_ind--;
  }
  token_ptr->token_id = ERROR;
  get_actual_token(token_str, token_ind);
  strcpy(token_ptr->token_string, token_str);
  return (MARK(9, 1), (token_ptr));
}

/* *********************************************************************
   Function name : check_delimiter
   Input         : character
   Output        : boolean
   Exceptions    : none.
   Description   : This function checks for the delimiter. If ch is not
                   alphabet and non numeric then it returns TRUE else
                   it returns FALSE.
 * ******************************************************************* */

static int check_delimiter(int ch) {
  if (!(MARK(10, 4), isalpha(ch)) &&
      !(mark(10, 3), isdigit(ch))) { /* Check for digit and alpha */
    return (MARK(10, 2), (TRUE));
  }
  return (MARK(10, 1), (FALSE));
}

/* ********************************************************************
   Function name : keyword
   Input         : state of the DFA
   Output        : Keyword.
   Exceptions    : If the state doesn't represent a keyword it exits.
   Description   : According to the final state specified by state the
                   respective token_id is returned.
 * ***************************************************************** */

static int keyword(int state) {
  switch (
      (MARK(11, 2), state)) { /* Return the respective macro for the Keyword. */
  case 6:
    return (MARK(11, 8), (LAMBDA));
  case 9:
    return (MARK(11, 7), (AND));
  case 11:
    return (MARK(11, 6), (OR));
  case 13:
    return (MARK(11, 5), (IF));
  case 16:
    return (MARK(11, 4), (XOR));
  default:
    (mark(11, 3), fprintf(stdout, "error\n"));
    break;
  }
  (MARK(11, 1), exit(0));
}

/* ********************************************************************
   Function name : special
   Input         : The state of the DFA.
   Output        : special symbol.
   Exceptions    : if the state doesn't belong to a special character
                   it exits.
   Description   : This function returns the token_id according to the
                   final state given by state.
 * ****************************************************************** */

static int special(int state) {
  switch (
      (MARK(12, 2),
       state)) { /* return the respective macro for the special character. */
  case 19:
    return (MARK(12, 11), (LPAREN));
  case 20:
    return (MARK(12, 10), (RPAREN));
  case 21:
    return (MARK(12, 9), (LSQUARE));
  case 22:
    return (MARK(12, 8), (RSQUARE));
  case 23:
    return (MARK(12, 7), (QUOTE));
  case 24:
    return (MARK(12, 6), (BQUOTE));
  case 25:
    return (MARK(12, 5), (COMMA));
  case 32:
    return (MARK(12, 4), (EQUALGREATER));
  default:
    (mark(12, 3), fprintf(stdout, "error\n"));
    break;
  }
  (MARK(12, 1), exit(0));
}

/* **********************************************************************
   Function name : skip
   Input         : character_stream
   Output        : void.
   Exceptions    : none.
   Description   : This function skips the comment part of the program.
                   It takes charcter_stream as input and reads character
                   until it finds new line character or
                   end_of_character_stream.
 * ******************************************************************* */

static void skip(character_stream stream_ptr) {
  MARK(13, 7);
  char c;

  while ((c = (MARK(13, 6), get_char(stream_ptr))) != '\n' &&
         !(mark(13, 5), is_end_of_character_stream(stream_ptr)))
    ; /* Skip the characters until EOF or EOL found. */
  if ((mark(13, 3), c == EOF)) {
    (mark(13, 2),
     unget_char(c, stream_ptr)); /* Put back to leave gracefully - hf */
  }
  MARK(13, 1);
  return;
}

/* *********************************************************************
   Function name : constant
   Input         : state of DFA, Token string, Token id.
   Output        : constant token.
   Exceptions    : none.
   Description   : This function returns the token_id for the constatnts
                   speccified by  the final state.
 * ****************************************************************** */

static int constant(int state, char token_str[], int token_ind) {
  switch ((MARK(14, 2), state)) { /* Return the respective CONSTANT macro. */
  case 27:
    return (MARK(14, 5), (STRING_CONSTANT));
  case 29:
    token_str[token_ind - 2] = ' ';
    return (MARK(14, 4), (CHARACTER_CONSTANT));
  default:
    break;
  }
  int result_c0236bd9f0 = (ERROR);
  return (MARK(14, 1), (result_c0236bd9f0));
}

/* *******************************************************************
   Function name : next_state
   Input         : current state, character
   Output        : next state of the DFA
   Exceptions    : none.
   Description   : This function returns the next state in the transition
                   diagram. The next state is determined by the current
                   state state and the inpu character ch.
 * ****************************************************************** */

static int next_state(int state, int ch) {
  if ((MARK(15, 7), state < 0)) {
    return (MARK(15, 6), (state));
  }
  if ((mark(15, 5), base[state] + ch >= 0)) {
    if ((mark(15, 4),
         check[base[state] + ch] == state)) { /* Check for the right state */
      int result_83805badd4 = (next[base[state] + ch]);
      return (MARK(15, 3), (result_83805badd4));
    } else {
      int result_f8420b293c = (next_state(default1[state], ch));
      return (MARK(15, 2), (result_f8420b293c));
    }
  } else {
    int result_1288f3bd0b = (next_state(default1[state], ch));
    return (MARK(15, 1), (result_1288f3bd0b));
  }
}

/* *********************************************************************
   Function name : is_eof_token
   Input         : token
   Output        : Boolean
   Exceptions    : none.
   Description   : This function checks whether the token t is eof_token
                   or not. If the integer value stored in the t is
                   EOTSTREAM then it is eof_token.
 * ***************************************************************** */

int is_eof_token(token t) {
  if ((MARK(16, 3), t->token_id == EOTSTREAM)) {
    return (MARK(16, 2), (TRUE));
  }
  return (MARK(16, 1), (FALSE));
}

/* ********************************************************************
   Function name : print_token
   Input         : token
   Output        : Boolean
   Exceptions    : none.
   Description   : This function  prints the token. The token_id gives
                   the type of token not the token itself. So, in the
                   case of identifier,numeric,  string,character it is
                   required to print the actual token  from token_str.
                   So, precaution must be taken when printing the token.
                   This function is able to print the current token only
                   and it is the limitation of the program.
 * ******************************************************************** */

int print_token(token token_ptr) {
  switch (
      (MARK(17, 2), token_ptr->token_id)) { /* Print the respective tokens. */
  case ERROR:
    fprintf(stdout, "error,\t\"");
    fprintf(stdout, "%s", token_ptr->token_string);
    fprintf(stdout, "\".\n");
    return (MARK(17, 22), (TRUE));
  case EOTSTREAM:
    fprintf(stdout, "eof.\n");
    return (MARK(17, 21), (TRUE));
  case 6:
    fprintf(stdout, "keyword,\t\"lambda\".\n");
    return (MARK(17, 20), (TRUE));
  case 9:
    fprintf(stdout, "keyword,\t\"and\".\n");
    return (MARK(17, 19), (TRUE));
  case 11:
    fprintf(stdout, "keyword,\t\"or\".\n");
    return (MARK(17, 18), (TRUE));
  case 13:
    fprintf(stdout, "keyword,\t\"if\".\n");
    return (MARK(17, 17), (TRUE));
  case 16:
    fprintf(stdout, "keyword,\t\"xor\".\n");
    return (MARK(17, 16), (TRUE));
  case 17:
    fprintf(stdout, "identifier,\t\"");
    fprintf(stdout, "%s", token_ptr->token_string);
    fprintf(stdout, "\".\n");
    return (MARK(17, 15), (TRUE));
  case 18:
    fprintf(stdout, "numeric,\t");
    fprintf(stdout, "%s", token_ptr->token_string);
    fprintf(stdout, ".\n");
    return (MARK(17, 14), (TRUE));
  case 19:
    fprintf(stdout, "lparen.\n");
    return (MARK(17, 13), (TRUE));
  case 20:
    fprintf(stdout, "rparen.\n");
    return (MARK(17, 12), (TRUE));
  case 21:
    fprintf(stdout, "lsquare.\n");
    return (MARK(17, 11), (TRUE));
  case 22:
    fprintf(stdout, "rsquare.\n");
    return (MARK(17, 10), (TRUE));
  case 23:
    fprintf(stdout, "quote.\n");
    return (MARK(17, 9), (TRUE));
  case 24:
    fprintf(stdout, "bquote.\n");
    return (MARK(17, 8), (TRUE));
  case 25:
    fprintf(stdout, "comma.\n");
    return (MARK(17, 7), (TRUE));
  case 27:
    fprintf(stdout, "string,\t");
    fprintf(stdout, "%s", token_ptr->token_string);
    fprintf(stdout, ".\n");
    return (MARK(17, 6), (TRUE));
  case 29:
    fprintf(stdout, "character,\t\"");
    fprintf(stdout, "%s", token_ptr->token_string);
    fprintf(stdout, "\".\n");
    return (MARK(17, 5), (TRUE));
  case 32:
    fprintf(stdout, "keyword,\t\"=>\".\n");
    return (MARK(17, 4), (TRUE));
  default:
    break;
  }
  return (MARK(17, 1), (FALSE));
}

/* **********************************************************************
   Function name : get_actual_token
   Input         : token string and token id.
   Output        : void.
   Exceptions    : none.
   Description   : This function prints the actual token in the case of
                   identifier,numeric,string and character. It removes
                   the leading and trailing  spaces and prints the token.
 * ****************************************************************** */

static void get_actual_token(char token_str[], int token_ind) {
  MARK(18, 14);
  int ind, start;

  for (ind = token_ind;
       (MARK(18, 13), ind > 0) && (mark(18, 12), isspace(token_str[ind - 1]));
       (mark(18, 11), --ind))
    ;
  /* Delete the trailing white spaces & protect - hf */
  (mark(18, 10), token_str[ind] = '\0');
  token_ind = ind;
  for (ind = 0; (MARK(18, 9), ind < token_ind); (mark(18, 6), ++ind))
    if (!(mark(18, 8), isspace(token_str[ind]))) {
      break;
    }
  for ((mark(18, 5), start = 0); (MARK(18, 4), ind <= token_ind);
       (mark(18, 2), ++start), ++ind) /* Delete the leading
white spaces. */
  {
    (mark(18, 3), token_str[start] = token_str[ind]);
  }
  MARK(18, 1);
  return;
}
