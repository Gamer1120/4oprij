package test;

import game.Disc;

import java.io.IOException;
import java.net.InetAddress;

import client.Client;
import client.ClientTUI;

public class ClientTest {
	// HOW TO SETUP THIS TEST
	// 1. Launch ServerGUI on port 2727.
	// 2. Run a ClientTUI. Enter localhost for the IP, 2727 for the port and -N TestOpponent as name.
	// 3. Run this test.
	public static void main(String[] args) {
		Client cl = null;
		try {
			cl = new Client(InetAddress.getByName("localhost"), 2727,
					new ClientTUI());
		} catch (IOException e) {
			System.out
					.println("Couldn't create a client. Did you turn on the server?");
		}
		cl.setUpPlayer("ClientTest");
		System.out
				.println("The name of this Client should be ClientTest. It acutally is: "
						+ cl.getClientName());
		cl.sendMessage(Client.CONNECT + " " + cl.getClientName());
		cl.sendMessage(Client.PING);
		cl.sendMessage(Client.PING);
		cl.sendMessage(Client.PING);
		System.out
				.println("On the console of the server, it should say that ClientTest has connected, sent 3 pings and left.");
		System.out.println("From now on, faking client commands.");
		System.out.println(Client.HELP + ":");
		cl.clientHelp();
		System.out.println(Client.MOVE + ":");
		cl.clientMove(Client.MOVE + " 1", (Client.MOVE + " 1").split("\\s+"));
		System.out.println(Client.INVITE + ":");
		cl.clientInvite(Client.INVITE + " lalala",
				(Client.INVITE + " lalala").split("\\s+"));
		cl.clientInvite(Client.INVITE + " lalala",
				(Client.INVITE + " lalala 8").split("\\s+"));
		cl.clientInvite(Client.INVITE + " lalala 10 10",
				(Client.INVITE + " lalala 10 10").split("\\s+"));
		System.out.println("ACCEPT_INVITE:");
		cl.clientAccept(Client.ACCEPT_INVITE,
				(Client.ACCEPT_INVITE).split("\\s+"));
		cl.clientAccept(Client.ACCEPT_INVITE + " nobody lol",
				(Client.ACCEPT_INVITE + " nobody lol").split("\\s+"));
		System.out.println("DECLINE_INVITE");
		cl.clientDecline(Client.DECLINE_INVITE,
				Client.DECLINE_INVITE.split("\\s+"));
		cl.clientDecline(Client.DECLINE_INVITE + " nobody lol",
				(Client.DECLINE_INVITE + " nobody lol").split("\\s+"));
		System.out.println(Client.HINT + ":");
		cl.clientHint();
		cl.clientRequestBoard();
		System.out.println("isConnected() == " + cl.isConnected());
		System.out.println("isIngame() == " + cl.isIngame());
		System.out.println("getBoard() == " + cl.getBoard());
		System.out
				.println("cl.arrayToLine((\"This is a line.\").split(regex); == "
						+ cl.arrayToLine("This is a line.".split("\\s+"))
						+ " Expected:  is a line.");
		System.out.println("Adding a server invite from Test with default board size");
		cl.addServerInvite("Test");
		System.out.println("Adding a server invite from Test with custom board size");
		cl.addServerInvite("Test", 4, 4);
		System.out.println("Removing a server invite from Test");
		cl.removeServerInvite("Test");
		Client clNaiveWithoutName = null;
		try {
			clNaiveWithoutName = new Client(InetAddress.getByName("localhost"),
					2727, new ClientTUI());
		} catch (IOException e) {
			System.out
					.println("Couldn't create a client. Did you turn on the server?");
		}
		clNaiveWithoutName.setUpPlayer("-N");
		System.out
				.println("Created a ComputerPlayer with a NaiveStrategy without name.");
		Client clSmartWithoutName = null;
		try {
			clSmartWithoutName = new Client(InetAddress.getByName("localhost"),
					2727, new ClientTUI());
		} catch (IOException e) {
			System.out
					.println("Couldn't create a client. Did you turn on the server?");
		}
		clSmartWithoutName.setUpPlayer("-S");
		System.out
				.println("Created a ComputerPlayer with a SmartStrategy without name.");
		Client clMinMaxWithoutName = null;
		try {
			clMinMaxWithoutName = new Client(
					InetAddress.getByName("localhost"), 2727, new ClientTUI());
		} catch (IOException e) {
			System.out
					.println("Couldn't create a client. Did you turn on the server?");
		}
		clMinMaxWithoutName.setUpPlayer("-M");
		System.out
				.println("Created a ComputerPlayer with a MinMaxStrategy without name.");
		Client clNaiveWithName = null;
		try {
			clNaiveWithName = new Client(InetAddress.getByName("localhost"),
					2727, new ClientTUI());
		} catch (IOException e) {
			System.out
					.println("Couldn't create a client. Did you turn on the server?");
		}
		clNaiveWithName.setUpPlayer("-N ClientTest");
		System.out
				.println("Created a ComputerPlayer with a NaiveStrategy with the name ClientTest.");
		Client clSmartWithName = null;
		try {
			clSmartWithName = new Client(InetAddress.getByName("localhost"),
					2727, new ClientTUI());
		} catch (IOException e) {
			System.out
					.println("Couldn't create a client. Did you turn on the server?");
		}
		clSmartWithName.setUpPlayer("-S ClientTest");
		System.out
				.println("Created a ComputerPlayer with a SmartStrategy with the name ClientTest.");
		Client clMinMaxWithName = null;
		try {
			clMinMaxWithName = new Client(InetAddress.getByName("localhost"),
					2727, new ClientTUI());
		} catch (IOException e) {
			System.out
					.println("Couldn't create a client. Did you turn on the server?");
		}
		clMinMaxWithName.setUpPlayer("-M ClientTest");
		System.out
				.println("Created a ComputerPlayer with a MinMaxStrategy with the name ClientTest.");
		System.out.println("Using the toBoard when myNumber is not set gives: "
				+ cl.toBoard("4 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0"));
		System.out
				.println("Using the makeBoard on an empty board of 4x4 gives: "
						+ cl.makeBoard(4, 4, Disc.YELLOW, Disc.RED,
								"BOARD 4 4 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0".split(" ")));
		System.out
		.println("Using the makeBoard on an filled board of 4x4 gives: "
				+ cl.makeBoard(4, 4, Disc.YELLOW, Disc.RED,
						"BOARD 4 4 1 2 2 1 1 2 1 1 2 2 2 1 1 1 2 1".split(" ")));
		cl.start();
		cl.shutdown();
	}

}
