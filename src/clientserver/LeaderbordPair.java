package clientserver;

import java.io.Serializable;

public class LeaderbordPair implements Comparable<LeaderbordPair>, Serializable {

	/**
	 * Auto generated serial UID for Serializable.
	 */
	private static final long serialVersionUID = 4797121270035180883L;
	private String name;
	private int score;

	public LeaderbordPair(String name, int score) {
		this.name = name;
		this.score = score;
	}

	public String getName() {
		return name;
	}

	public int getScore() {
		return score;
	}

	public void incrementScore() {
		score += 1;
	}

	public void decrementScore() {
		score -= 1;
	}

	public int compareTo(LeaderbordPair pair) {
		if (this.getScore() > pair.getScore()) {
			return 1;
		} else if (this.getScore() < pair.getScore()) {
			return -1;
		} else {
			return this.getName().compareTo(pair.getName());
		}
	}

	public boolean equals(Object o) {
		if (o instanceof LeaderbordPair) {
			return name.equals(((LeaderbordPair) o).getName())
					&& score == ((LeaderbordPair) o).getScore();
		} else {
			return false;
		}
	}
}
