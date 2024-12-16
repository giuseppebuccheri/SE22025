-- SIGNATURES
open util/integer

sig User {
    email: one Email,
    password: one Password
}

sig Student extends User {
    name: one Name,
    surname: one Surname,
    academicEmail: one Email,
    university: one University,
    phoneNumber: one PhoneNumber,
    postalCode: one PostalCode,
    cv: one CV,
    goals: set Goal,
    matches: set Match,
    ongoingInternship: lone Internship,
    terminatedInternships: set Internship,
}

sig Company extends User {
    fullName: one FullName,
    phoneNumber: one PhoneNumber,
    officeAddress: one OfficeAddress,
    postedOffers : set InternshipOffer    
}

sig University extends User {
    ongoingInternships: set Internship,
    terminatedInternships: set Internship
}

sig Internship {
    company: one Company,
    student: one Student,
    status: one Status,
    complaints: set Complaint,
    feedback: set Feedback,
    offer: one InternshipOffer
}

sig InternshipOffer {
    project: one Project,
    role: one Text,
    officeAddress: one OfficeAddress,
    numStudents: lone Int,
    salary: lone Salary,
    skills: set Skill,
    schedule: one Schedule,
    benefits: set Benefit,
    applicants: set Student,
    selectedStudents: set Student
}

sig Match {
    student: one Student,
    score: one Score,
    offer: one InternshipOffer
}

sig Complaint {
    student: lone Student,
    company: lone Company,
    internship: one Internship,
    text: one Text
}

sig Feedback {
    student: lone Student,
    company: lone Company,
    internship: one Internship,
    text: one Text
}

abstract sig Email {}
abstract sig Password {}

abstract sig Name {}
abstract sig Surname {}
abstract sig PhoneNumber {}
abstract sig PostalCode {}
abstract sig CV {}
abstract sig Goal {}

abstract sig FullName {}
abstract sig OfficeAddress {}
abstract sig Project {}
abstract sig Salary {}
abstract sig Skill {}
abstract sig Schedule {}
abstract sig Benefit {}

abstract sig Score {}

abstract sig Text {}

abstract sig Status {}
one sig Proposed, Ongoing, Terminated extends Status {}

-- FACTS

-- Only one status can be applied to each internship at a time
fact internshipHasOneStatus {
    all i: Internship | one i.status
}

-- There must be no users using the same email
fact noUsersWithSameEmail {
    no disj u1, u2: User | u1.email = u2.email
}

-- There must be no Students using the same academic email
fact noStudentsWithSameAcademicEmail {
    no disj s1, s2: Student | s1.academicEmail = s2.academicEmail
}

--A terminated internship can be found in the university parameter of the student who completed it
fact terminatedInternshipConsistency {
    all i: Internship |
        i.status = Terminated implies
        one u: University | i in u.terminatedInternships
}

-- An academic email used by a student cannot be used as a general email by another user
fact academicEmailConsistency {
    no disj s: Student, u: User |
        s.academicEmail = u.email
}

--The ongoin Internship must be reflected in the student parameters
fact ongoingInternshipStatusConsistency {
    all i: Internship | 
        i.status = Ongoing implies i.student.ongoingInternship = i
}

-- There must be no Students using the same phone number
fact noStudentsWithSamePhoneNumber {
    no disj s1, s2: Student | s1.phoneNumber = s2.phoneNumber
}

-- There must be no Companies using the same phone number or office address
fact noDuplicatedCompanies {
    no disj c1, c2: Company | c1.phoneNumber = c2.phoneNumber
        or c1.officeAddress = c2.officeAddress
}

-- A student cannot have more than one ongoing internship
fact oneOngoingInternshipPerStudent {
    all s: Student | lone s.ongoingInternship
}

-- A student cannot apply for the same internship offer more than once
fact uniqueApplications {
    all s: Student, o: InternshipOffer |
        s in o.applicants implies lone o.applicants & s
}

-- A student cannot choosen for the same internship offer more than once
fact noDuplicateApplications {
    all o: InternshipOffer |
        all s: Student | 
            s in o.applicants implies s not in o.selectedStudents
}

--An InternshipOffer can only belong to a single company
fact eachOfferBelongsToOneCompany {
    all o: InternshipOffer | one c: Company | o in c.postedOffers
}

-- An internship can only reference an offer posted by the associated company
fact internshipOfferCompanyConsistency {
    all i: Internship | 
        i.offer in i.company.postedOffers
}

-- A match must involve a valid student and a valid offer
fact validMatchReferences {
    all m: Match |
        m.student in Student and m.offer in InternshipOffer
}

-- A student cannot have multiple matches for the same offer
fact uniqueMatchPerStudentOffer {
    no disj m1, m2: Match |
        m1.student = m2.student and m1.offer = m2.offer
}

-- A student cannot apply for internships they are already matched with
fact noApplicationsForMatchedInternships {
    all m: Match | 
        m.student !in m.offer.applicants
}

--An ongoing or terminated internship has already selected some applicants
fact selectedApplicantsNotEmpty {
    all i: Internship |
        i.status in Ongoing + Terminated implies some i.offer.selectedStudents
}

-- Complaints must always reference their related internship
fact complaintConsistency {
    all c: Complaint | 
        c.internship.student = c.student and
        c.internship.company = c.company
}

-- Feedback must always reference its related internship
fact feedbackConsistency {
    all f: Feedback | 
        f.internship.student = f.student and
        f.internship.company = f.company
}

-- Both the student and the company must provide feedback for terminated internships
fact feedbackCompleteness {
    all i: Internship | 
        i.status = Terminated implies 
        some f1,f2 : Feedback | 
		f1.internship = i and f2.internship = i and f1.student != none and f2.company != none
}

-- A terminated internship must belong to the student's terminated internships set
fact terminatedInternshipsTracking {
    all i: Internship | 
        i.status = Terminated implies i in i.student.terminatedInternships
}

-- Universities can only manage internships they are assigned to
fact universityInternshipOwnership {
    all u: University |
        u.ongoingInternships + u.terminatedInternships in Internship
}

-- the number of selected applicants must be less than or equal to the number of open positions
fact selectedStudentsLimit {
    all o: InternshipOffer |
        #o.selectedStudents <= o.numStudents
}

-- Only ongoing internships can be assigned to a university
fact universityOngoingInternshipTracking {
    all i: Internship |
        i.status = Ongoing implies i in University.ongoingInternships
}

--If an internship offer has multiple positions open then all the individual internships are the same and have the same status at all time
fact consistentInternshipsForOffer {
    all o: InternshipOffer |
        o.numStudents > 1 implies
        all i1, i2: Internship | 
            i1 != i2 and i1.offer = o and i2.offer = o implies {
                // Internships connected to the same offer have the same status
                i1.status = i2.status and
                // Internships connected to the same offer have the same parameters (except student)
                i1.company = i2.company and
                i1.complaints = i2.complaints and
                i1.feedback = i2.feedback and
                // Students must be different
                i1.student != i2.student
            }
}

-- No offer can have selected students exceeding the number of required students
fact noExceedSelectedStudents {
    all o: InternshipOffer | 
        (o.numStudents != none implies #o.selectedStudents <= o.numStudents) or
	(o.numStudents = none implies #o.selectedStudents <= 0)
}

-- PREDICATES

pred UsersWorld{
    #Student = 5
  	#Company = 4
	#University = 2
}
run UsersWorld for 8

pred InternshipsWorld {
    #Internship >= 3
    #InternshipOffer >= 3
    #Company >= 2
}
run InternshipsWorld for 5

pred ApplicationsWorld {
    #Student >= 3
    #Internship >= 3
    #InternshipOffer >= 3
}
run ApplicationsWorld for 5

pred FeedbackComplaintWorld {
    #Company >= 3
    #University >= 2
    #Feedback >= 2
    #Complaint >= 2
}
run FeedbackComplaintWorld for 5