package ss.week5;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

public class MapUtil {
	// * Checks whether a map is 1-1
	
	 /*@ ensures (\forall K x1,x2; map.keySet().contains(x1) && map.keySet().contains(x2)
	 @ && !map.get(x1).equals(map.get(x2)) && x1.equals(x2)) == \result;
	 */
	public static <K, V> boolean isOneOnOne(Map<K, V> map) {
		Set<K> setkeys = map.keySet();
		Collection<V> values = map.values();
		Iterator<V> itVal = values.iterator();
		while (itVal.hasNext()) {
			int sum = 0;
			Object test = itVal.next();
			Iterator<K> itKey = setkeys.iterator();
			while (itKey.hasNext()) {
				Object comp = map.get(itKey.next());
				if (comp.equals(test)) {
					sum = sum + 1;
				}
			}
			if (sum > 1) {
				return false;
			}
		}
		return true;
	}

	
	 /*@ ensures (\forall V v1; range.contains(v1) && map.values().contains(v1)) == \result;
	 */
	public static <K, V> boolean isSurjectiveOnRange(Map<K, V> map, Set<V> range) {
		Set<K> setkeys = map.keySet();
		Set<V> values = range;
		Iterator<V> itVal = values.iterator();
		while (itVal.hasNext()) {
			int sum = 0;
			Object test = itVal.next();
			Iterator<K> itKey = setkeys.iterator();
			while (itKey.hasNext()) {
				Object comp = map.get(itKey.next());
				if (comp.equals(test)) {
					sum = sum + 1;
				}
			}
			if (sum < 1) {
				return false;
			}
		}
		return true;
	}

	//@ ensures (\forall V v; map.values().contains(v) && \result.keySet().contains(v));
	//@ ensures (\forall K k; map.keySet().contains(k) && \result.values().contains(k));
	
	//@ ensures (\forall K k; map.keySet().contains(k); \result.get(map.get(k)).contains(k));
	public static <K, V> Map<V, Set<K>> inverse(Map<K, V> map) {
		Map<V, Set<K>> finalmap = new HashMap<V, Set<K>>();		
		for (V value: map.values()) {
			if (!finalmap.keySet().contains(value)) {
				Set<K> keysOfVal = new HashSet<K>();
				for (K key: map.keySet()) {
					if (map.get(key).equals(value)) {
						keysOfVal.add(key);
					}
				}
				finalmap.put(value, keysOfVal);
			}
		}
		return finalmap;
	}

	//@ ensures (\forall V v; map.values().contains(v) && \result.keySet().contains(v));
	//@ ensures (\forall K k; map.keySet().contains(k) && \result.values().contains(k));
	
	//@ ensures (\forall K k; map.keySet().contains(k); \result.get(map.get(k)) == k);
	public static <K, V> Map<V, K> inverseBijection(Map<K, V> map) {
		// if isOneOnOne && isSurjectiveOnRange then there must be 
		// the same number of keys and values.
		if (isOneOnOne(map)) {
			Map<V, K> finalmap = new HashMap<V, K>();
			for (K key: map.keySet()) {
				finalmap.put(map.get(key), key);
			}
			return finalmap;
		}
		return null;
	}
	
	// using iterator:
	/* Set<K> setkeys = map.keySet();
	Iterator<K> itKey = setkeys.iterator();
	while (itKey.hasNext()) {
		K key = itKey.next();
		finalmap.put(map.get(key), key);
	} */

	//@ ensures (\forall V v; f.values().contains(v); g.keySet().contains(v)); 
	public static <K, V, W> boolean compatible(Map<K, V> f, Map<V, W> g) {
		Set<V> keysg = g.keySet();
		boolean compatible = true;
		for (V valuesf: f.values()) {
			if (!keysg.contains(valuesf)) {
				compatible = false;
			}
		}
		return compatible;
	}

	//@ ensures (\forall K k; \result.keySet().contains(k); \result.get(k) == g.get(f.get(k)));
	public static <K, V, W> Map<K, W> compose(Map<K, V> f, Map<V, W> g) {
		if (compatible(f, g)) {
			Map<K, W> finalmap = new HashMap<K, W>();
			for (K keyf: f.keySet()) {
				finalmap.put(keyf, g.get(f.get(keyf)));
			}
			return finalmap;			
		}
		return null;
	}
}
