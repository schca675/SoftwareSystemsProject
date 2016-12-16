package ss.week4;

import java.util.*;

public class MergeSort {
	// @ requires a non null list.
	public static <Elem extends Comparable<Elem>> void mergesort(List<Elem> list) {
		if (list.size() != 0 && list.size() != 1) {
			int mid = list.size() / 2;
			List<Elem> first = new ArrayList<Elem>(list.subList(0, mid));
			List<Elem> last = new ArrayList<Elem>(list.subList(mid, list.size()));
			mergesort(first);
			mergesort(last);
			List<Elem> res = new ArrayList<Elem>();
			int fi = 0;
			int si = 0;
			while (fi < first.size() && si < last.size()) {
				if (first.get(fi).compareTo(last.get(si)) < 0) {
					res.add(first.get(fi));
					fi = fi + 1;
				} else {
					res.add(last.get(si));
					si = si + 1;
				}
			}
			if (fi < first.size() && fi >= 0) {
				List<Elem> rest = first.subList(fi, first.size());
				res.addAll(rest);
			} else if (si < last.size() && si >= 0) {
				List<Elem> rest = last.subList(si, last.size());
				res.addAll(rest);
			}
			list.clear();
			list.addAll(res);
		}

	}
}
