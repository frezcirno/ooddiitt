#include "mark.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tokens.h"

#define START 5
#define TRUE 1
#define FALSE 0

token numeric_case();
token error_or_eof_case();
int check_delimiter();
int keyword(int state);
int special(int state);
void skip(usher_t *usher, character_stream stream_ptr);
int constant(int state, char token_str[], int token_ind);
int next_state();
void get_actual_token(usher_t *usher, char token_str[], int token_ind);

int print_token(token token_ptr);
void unget_char(int ch, character_stream stream_ptr);

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

token get_token(usher_t *usher, token_stream tstream_ptr) {
  MARK(7, 34);
  char token_str[80]; /* This buffer stores the current token */
  int token_ind;      /* Index to the token_str  */
  token token_ptr;
  char ch;
  int cu_state, next_st, token_found;

  token_ptr = (token)(malloc(sizeof(struct token_type)));
  ch = get_char(tstream_ptr->ch_stream);
  cu_state = token_ind = token_found = 0;
  while ((MARK(7, 33), !guide(usher, token_found))) {
    if ((mark(7, 32), guide(usher, token_ind < 80))) { /* ADDED ERROR CHECK - hf */
      (mark(7, 31), token_str[token_ind++] = ch);
      next_st = next_state(cu_state, ch);
    } else {
      (mark(7, 30), next_st = -1); /* - hf */
    }
    if ((mark(7, 29), guide(usher, next_st == -1))) { /* ERROR or EOF case */
      token result_4882dff095 = (error_or_eof_case(
          tstream_ptr, token_ptr, cu_state, token_str, token_ind, ch));
      return (MARK(7, 28), (result_4882dff095));
    } else if ((mark(7, 27), guide(usher, next_st == -2))) { /* This is numeric case. */
      token result_8025f5e6e0 =
          (numeric_case(tstream_ptr, token_ptr, ch, token_str, token_ind));
      return (MARK(7, 26), (result_8025f5e6e0));
    } else if ((mark(7, 25), guide(usher, next_st == -3))) { /* This is the IDENTIFIER case */
      token_ptr->token_id = IDENTIFIER;
      unget_char(ch, tstream_ptr->ch_stream);
      token_ind--;
      get_actual_token(NULL, token_str, token_ind);
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
      if (guide(usher, check_delimiter(ch) == TRUE)) {
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
      get_actual_token(NULL, token_str, token_ind);
      strcpy(token_ptr->token_string, token_str);
      return (MARK(7, 6), (token_ptr));
    case 30: /* This is COMMENT case */
      (mark(7, 5), skip(NULL, tstream_ptr->ch_stream));
      token_ind = next_st = 0;
      break;
    }
    (mark(7, 3), cu_state = next_st);
    ch = get_char(tstream_ptr->ch_stream);
  }
  return (MARK(7, 1), NULL);
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

void skip(usher_t *usher, character_stream stream_ptr) {
  MARK(13, 7);
  char c;

  while ( guide(usher, (c = (MARK(13, 6), get_char(stream_ptr))) != '\n') &&
         !(mark(13, 5), guide(usher, is_end_of_character_stream(stream_ptr))))
    ; /* Skip the characters until EOF or EOL found. */
  if ((mark(13, 3), guide(usher, c == EOF))) {
    (mark(13, 2),
     unget_char(c, stream_ptr)); /* Put back to leave gracefully - hf */
  }
  MARK(13, 1);
  return;
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

void get_actual_token(usher_t *usher, char token_str[], int token_ind) {
  MARK(18, 14);
  int ind, start;

  for (ind = token_ind;
       (MARK(18, 13), guide(usher, ind > 0)) && (mark(18, 12), guide(usher, isspace(token_str[ind - 1])));
       (mark(18, 11), --ind))
    ;
  /* Delete the trailing white spaces & protect - hf */
  (mark(18, 10), token_str[ind] = '\0');
  token_ind = ind;
  for (ind = 0; (MARK(18, 9), guide(usher, ind < token_ind)); (mark(18, 6), ++ind))
    if (!(mark(18, 8), guide(usher, isspace(token_str[ind])))) {
      break;
    }
  for ((mark(18, 5), start = 0); (MARK(18, 4), guide(usher, ind <= token_ind)); (mark(18, 2), ++start), ++ind)   {
    (mark(18, 3), token_str[start] = token_str[ind]);
  }
  MARK(18, 1);
  return;
}
