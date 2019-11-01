

#include <string>
#include <sstream>
#include <iomanip>
#include "klee/util/CommonUtil.h"

using namespace std;

namespace klee {

sys_clock::time_point to_time_point(const string &str) {

  tm _tm;
  stringstream ss(str);
  ss >> get_time(&_tm, "\"%FT%TZ\"");
  return sys_clock::from_time_t(mktime(&_tm));
}

string to_string(const sys_clock::time_point &tp) {

  auto itt = sys_clock::to_time_t(tp);
  ostringstream ss;
  ss << put_time(gmtime(&itt), "%FT%TZ");
  return ss.str();
}

string currentISO8601TimeUTC() {
  return to_string(sys_clock::now());
}

};
