package ss.week2;

public class ThreeWayLamp7 {

	public enum Setting {
		OFF, LOW, MEDIUM, HIGH
	};

	private Setting currentSetting;

	/*@ private invariant currentSetting==Setting.OFF  || currentSetting==Setting.LOW 
	 @ || currentSetting==Setting.HIGH || currentSetting==Setting.MEDIUM; */

	// @ ensures getSetting() == Setting.OFF;
	public ThreeWayLamp7() {
		currentSetting = Setting.OFF;
		assert currentSetting == Setting.OFF;
	}

	// @ ensures \result >=Setting.OFF && \result <=Setting.HIGH;
	/* @ pure */ public Setting getSetting() {
		return currentSetting;
	}

	// @ ensures getSetting()==(\old(getSetting()) + 1) % 4;
	//@ ensures \old(getSetting()) == Setting.OFF ==> getSetting() == Setting.LOW;
	public void switchSetting() {
		assert currentSetting == Setting.OFF  || currentSetting == Setting.LOW 
				|| currentSetting == Setting.HIGH || currentSetting == Setting.MEDIUM;
		switch (currentSetting) {
		   	case OFF:
				currentSetting = Setting.LOW;
				break;
			case LOW:
				currentSetting = Setting.MEDIUM;
				break;
			case MEDIUM:
				currentSetting = Setting.HIGH;
				break;
			case HIGH:
				currentSetting = Setting.OFF;
				break;
		}
	}

}
